"""Successor committees: standby members who mirror a charter version and succeed it.

A charter may name a successor committee (SPEC §3.7, §5.5). Its members are
*standby members*: while the version lives they store every binding a client
asks them to (MIRROR) and answer with a signed *mirror ack*; a witness of the
version creates a vote only with acks from a quorum of the committee (SPEC
§5.1). When the version is to be replaced -- cooperatively, because its members
froze and signed the next charter, or after a dead-man period of silence -- a
standby member signs the next charter and *fences*: it never stores anything
for that version again. The new version's members ADOPT from the signing
standby members' mirror logs, so they inherit every binding behind every vote
the old version ever cast, even if that version was only partitioned and comes
back.

Safety needs no clock: the dead-man period only decides when an honest standby
member is willing to sign without the version's cooperation.

With a ``store`` every state change is durable before the member answers, and a
restarted member reloads it. A restart also starts a new observation window, so a
member never declares a version dead because of heartbeats it missed while down.

What one client can make a member store is bounded like a witness's records
(SPEC §5.1, §5.2, §5.5): MIRROR takes an authorisation of at most 32 KiB, only
below generation 16, and at most ``MAX_MIRROR_TIDS`` transitions per sigil and
generation; a release entry needs a death proof of at most 128 KiB for a binding
the member holds. Each refusal only withholds an ack (no ack, no vote), which
costs liveness and never safety. The handover of STANDBY, like ADOPT, keeps every
entry it is given, each distinct one once.
"""

import json
import secrets

from .charter import MAX_CHARTER_BYTES, Registry, charter_body, charter_hash, quorum, sign_charter, signers
from .crypto import KeyPair
from .encoding import canonical
from .model import ack_payload, transition_id
from .proofs import proves_dead, verify_heartbeat
from .store import WitnessStore
from .witness import MAX_AUTH_BYTES, MAX_GEN, MAX_PROOF_BYTES, Rejected, _encoding, _too_big, authorises

# Distinct transitions a member mirrors per (sigil, generation). An honest owner binds
# one transition per generation, and re-pledges another only after the first expired
# unbound (SPEC §4 rule 3); only the owner can authorise its sigil, so the cap only
# ever limits an owner flooding its own sigil.
MAX_MIRROR_TIDS = 4


class StandbyStore(WitnessStore):
    """A standby member's durable state, in the witness store's append-only log.

    Kinds: ``pk``; ``standby`` (``{constellation, version, since}``); ``fenced``
    (``{constellation, version, charter}``: the successor it signed); ``mirror``
    (key ``"<version>|<sigil>"``, value the mirror log of that sigil).
    """

    def load(self) -> dict:
        state = {"pk": None, "standby": None, "fenced": None, "mirror": {}}
        for kind, key, value in self.db.execute("SELECT kind, key, value FROM log ORDER BY seq"):
            v = json.loads(value)
            if kind == "mirror":
                state["mirror"][key] = v
            elif kind in ("pk", "standby", "fenced"):
                state[kind] = v
        return state


def _members_snapshot_union(snapshots) -> dict:
    """The union of snapshot logs, as ADOPT reads it: malformed parts are skipped, and
    each distinct entry (by ``enc``) is kept once, in the order first seen. Honest
    predecessors hand over the same entries, so keeping repeats would multiply a
    sigil's log by the number of signers at every handover."""
    out: dict[str, list] = {}
    seen: dict[str, set] = {}
    for snap in snapshots:
        if not isinstance(snap, dict):
            continue
        for sigil, log in snap.items():
            if not (isinstance(sigil, str) and isinstance(log, list)):
                continue
            kept, have = out.setdefault(sigil, []), seen.setdefault(sigil, set())
            for e in log:
                if isinstance(e, dict):
                    k = _encoding(e)
                    if k not in have:
                        have.add(k)
                        kept.append(e)
    return out


def _bindings(mirror: dict) -> set:
    """The ``(sigil, gen, tid)`` of every bind entry of a mirror log that verifies."""
    out = set()
    for sigil, log in mirror.items():
        for e in log:
            if isinstance(e, dict) and e.get("kind") == "bind":
                b = authorises(sigil, e.get("auth", {}))
                if b is not None:
                    out.add((sigil, *b))
    return out


def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


class Standby:
    """One member of a successor committee, standing by for one charter version at a time."""

    def __init__(self, kp: KeyPair, registry: Registry, clock, *, store: StandbyStore | None = None):
        self.kp = kp
        self.pk = kp.pk
        self.registry = registry
        self.clock = clock
        self.cid: str | None = None
        self.version: int | None = None
        self.mirror: dict[str, list] = {}      # sigil -> log entries (handover evidence + mirrored)
        self.mirrored: set[tuple] = set()      # (sigil, gen, tid) of every verified binding stored
        self._tids: dict[tuple, int] = {}      # (sigil, gen) -> how many of them
        self.fenced_for: str | None = None     # hash of the one successor we signed
        self.heard: dict[str, int] = {}        # member pk -> when it last answered our challenge
        self.since: int | None = None          # start of our observation window
        self.store = store
        if store is not None:
            self._restore()

    # ------------------------------------------------------------ durability

    def _restore(self) -> None:
        state = self.store.load()
        if state["pk"] is None:
            self.store.append([("pk", "", self.pk)])
        elif state["pk"] != self.pk:
            raise ValueError("store belongs to a different key")
        sb = state["standby"]
        if sb is None:
            return
        self.cid, self.version = sb["constellation"], sb["version"]
        # A restart starts a new observation window (see the module docstring).
        self.since = max(sb["since"], int(self.clock()))
        prefix = f"{self.version}|"
        self.mirror = {k[len(prefix):]: v for k, v in state["mirror"].items() if k.startswith(prefix)}
        self._set_mirrored(_bindings(self.mirror))
        f = state["fenced"]
        if isinstance(f, dict) and (f.get("constellation"), f.get("version")) == (self.cid, self.version):
            self.fenced_for = f["charter"]

    def _persist(self, *entries) -> None:
        if self.store is not None:
            self.store.append(list(entries))

    def _set_mirrored(self, binds: set) -> None:
        self.mirrored, self._tids = set(), {}
        for b in binds:
            self._add_mirrored(*b)

    def _add_mirrored(self, sigil: str, gen: int, tid: str) -> None:
        if (sigil, gen, tid) not in self.mirrored:
            self.mirrored.add((sigil, gen, tid))
            self._tids[(sigil, gen)] = self._tids.get((sigil, gen), 0) + 1

    # ------------------------------------------------------------ standing by

    def _version_body(self, cid: str, version: int) -> dict:
        body = self.registry.charter(cid, version)
        succ = None if body is None else body.get("successor")
        if succ is None or self.pk not in succ["committee"]:
            raise ValueError("not a member of this version's successor committee")
        return body

    def enter(self, cid: str, version: int, snapshots: list) -> None:
        """STANDBY: stand by for ``(cid, version)`` with the evidence its members adopt.

        ``snapshots`` are the ones the version's members ADOPT (SPEC §5.4/§5.5): the
        freezing members' and previous committee's for a rotation, the signing
        standby members' for a succession, none for version 0. A member only moves
        forward, and acts for one version at a time.
        """
        if not isinstance(snapshots, list):
            raise ValueError("snapshots must be a list")
        if not _is_int(version):
            raise ValueError("version must be an integer")
        self._version_body(cid, version)
        if self.cid is not None:
            if (self.cid, self.version) == (cid, version):
                return  # a retried STANDBY
            if self.cid != cid or not _is_int(version) or version <= self.version:
                raise Rejected("already standing by for another version")
        # Like ADOPT, the handover keeps every entry it is given whatever its size:
        # dropping evidence could lose a sealed binding.
        mirror = _members_snapshot_union(snapshots)
        since = int(self.clock())
        self._persist(("standby", "", {"constellation": cid, "version": version, "since": since}),
                      *(("mirror", f"{version}|{s}", log) for s, log in mirror.items()))
        self.cid, self.version, self.since = cid, version, since
        self.mirror, self.fenced_for, self.heard = mirror, None, {}
        self._set_mirrored(_bindings(mirror))

    def _active(self) -> None:
        if self.cid is None:
            raise Rejected("not standing by")
        if self.fenced_for is not None:
            raise Rejected("fenced: this member signed a successor of the version")

    def mirror_bind(self, req: dict) -> dict:
        """MIRROR: store an owner-authorised binding and answer a signed mirror ack.

        ``req`` is a SPEND request (``sigil, header, home, lock, salt, unlock``)
        plus the ``version`` it is for. The ack attests that the binding is in our
        mirror log, durably, before it leaves.
        """
        self._active()
        if not isinstance(req, dict):
            raise Rejected("malformed request")
        if req.get("home") != self.cid or not _is_int(req.get("version")) or req["version"] != self.version:
            raise Rejected("not standing by for this constellation version")
        sigil = req.get("sigil")
        auth = {k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}
        big = _too_big(auth, MAX_AUTH_BYTES)
        if big:
            raise Rejected("authorisation too large")
        bound = authorises(sigil, auth) if big is not None else None
        if bound is None:
            raise Rejected("malformed request or lock not satisfied")
        gen, tid = bound
        if (sigil, gen, tid) not in self.mirrored:
            # A binding already stored is acknowledged again whatever these say: it costs nothing.
            if gen >= MAX_GEN:
                raise Rejected("generation limit reached for this sigil")
            if self._tids.get((sigil, gen), 0) >= MAX_MIRROR_TIDS:
                raise Rejected("too many transitions mirrored at this generation")
            log = self.mirror.get(sigil, []) + [{"kind": "bind", "gen": gen, "auth": auth}]
            self._persist(("mirror", f"{self.version}|{sigil}", log))  # durable before the ack leaves
            self.mirror[sigil] = log
            self._add_mirrored(sigil, gen, tid)
        a = {"constellation": self.cid, "version": self.version, "member": self.pk,
             "sigil": sigil, "gen": gen, "tid": tid}
        a["sig"] = self.kp.sign("mirror", ack_payload(a))
        return a

    def note_release(self, sigil: str, entry: dict) -> bool:
        """Store a release entry whose death proof verifies, for a binding we hold.

        Releases need no ack (they are not needed for safety); they let a successor
        see that a binding died instead of finding the record contested. Only a
        binding in our mirror log can die there: anyone can build headers that name
        a consumed input, so releases of other tids would be unbounded junk.
        """
        self._active()
        try:
            h, t, proof = entry["header"], entry["tid"], entry["proof"]
            ok = (isinstance(sigil, str) and entry.get("kind") == "release" and _is_int(entry.get("gen"))
                  and transition_id(h) == t and [sigil, entry["gen"]] in h["inputs"]
                  and (sigil, entry["gen"], t) in self.mirrored)
            big = _too_big(proof, MAX_PROOF_BYTES) if ok else None
            if big:
                raise Rejected("death proof too large")
            ok = ok and big is False and proves_dead(h, t, proof, self.registry)
        except (KeyError, TypeError, AttributeError, ValueError):
            ok = False
        if not ok:
            raise Rejected("invalid release evidence")
        log = self.mirror.get(sigil, [])
        if any(e.get("kind") == "release" and e.get("tid") == t for e in log):
            return False
        log = log + [{"kind": "release", "gen": entry["gen"], "tid": t, "header": h, "proof": proof}]
        self._persist(("mirror", f"{self.version}|{sigil}", log))
        self.mirror[sigil] = log
        return True

    # ------------------------------------------------------------ the dead man

    def observe(self, heartbeat, challenge: str) -> bool:
        """Record a member's answer to our ``challenge``; True if it counted."""
        try:
            body = self.registry.charter(self.cid, self.version)
            ok = (isinstance(heartbeat, dict) and heartbeat["constellation"] == self.cid
                  and _is_int(heartbeat["version"]) and heartbeat["version"] == self.version
                  and heartbeat["challenge"] == challenge
                  and heartbeat["witness"] in body["witnesses"] and verify_heartbeat(heartbeat))
        except (KeyError, TypeError):
            ok = False
        if ok:
            self.heard[heartbeat["witness"]] = int(self.clock())
        return ok

    def probe(self, witnesses) -> int:
        """Challenge each of ``witnesses`` (objects with ``heartbeat``); count valid answers."""
        if self.cid is None:
            return 0
        n = 0
        for w in witnesses:
            challenge = secrets.token_hex(16)
            try:
                hb = w.heartbeat(challenge)
            except Rejected:
                continue
            n += self.observe(hb, challenge)
        return n

    def dead(self) -> bool:
        """The dead-man condition (SPEC §5.5): for the last ``dead_man`` seconds we have
        stood by, fewer than a quorum of the version's members have answered."""
        if self.cid is None:
            return False
        body = self.registry.charter(self.cid, self.version)
        if body is None:  # a registry older than our store: never declare it dead
            return False
        d = body["successor"]["dead_man"]
        now = int(self.clock())
        alive = {pk for pk, t in self.heard.items() if now - t <= d}
        return now - self.since >= d and len(alive) < quorum(len(body["witnesses"]))

    def succeed(self, next_charter: dict, sigs: dict | None = None) -> tuple[str, dict]:
        """SUCCEED: sign the next charter version and fence; returns (signature, snapshot).

        Signs only a well-formed successor of the version we stand by for, at most
        one, and only cooperatively (``sigs`` holds a quorum of the version's members'
        signatures on it) or once the dead-man condition holds. Asked again for the
        same successor, answers the same.
        """
        if self.cid is None:
            raise Rejected("not standing by")
        cur = self.registry.charter(self.cid, self.version)
        if cur is None:
            raise Rejected("own charter version unknown")
        try:
            well_formed = (next_charter == charter_body(next_charter["name"], next_charter["version"],
                                                        next_charter["witnesses"], next_charter["prev"],
                                                        next_charter.get("successor"))
                           and all(isinstance(k, str) for k in next_charter["witnesses"]))
        except (KeyError, TypeError, ValueError, AttributeError):
            well_formed = False
        if not well_formed:
            raise ValueError("malformed charter body")
        if len(canonical({"body": next_charter, "sigs": {}})) > MAX_CHARTER_BYTES:
            # Never valid (SPEC §3.7): fencing for it would leave us unable to sign any successor.
            raise Rejected("charter too large")
        if (next_charter["prev"] != charter_hash(cur) or not _is_int(next_charter["version"])
                or next_charter["version"] != self.version + 1):
            raise Rejected("charter does not extend the version we stand by for")
        h = charter_hash(next_charter)
        if self.fenced_for is not None:
            if self.fenced_for != h:
                raise Rejected("already signed a different successor")
        else:
            sigs = sigs if isinstance(sigs, dict) else {}
            ws = cur["witnesses"]
            cooperative = len(signers(next_charter, sigs, ws)) >= quorum(len(ws))
            if not cooperative and not self.dead():
                raise Rejected("the version is alive: no quorum of its members asked, "
                               "and the dead-man period has not passed")
            self._persist(("fenced", "", {"constellation": self.cid, "version": self.version, "charter": h}))
            self.fenced_for = h
        return sign_charter(self.kp, next_charter), self.snapshot()

    # ----------------------------------------------------------------- query

    def snapshot(self) -> dict:
        """Our mirror log, in FREEZE snapshot format (SPEC §5.4)."""
        return {s: list(log) for s, log in self.mirror.items()}

    def info(self) -> dict:
        return {"pk": self.pk, "role": "standby", "constellation": self.cid, "version": self.version,
                "fenced": self.fenced_for is not None}
