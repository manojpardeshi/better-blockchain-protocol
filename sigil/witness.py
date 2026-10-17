"""The witness: the only network role in Sigil.

A witness answers one question: "may this sigil be consumed by this
transition?" It checks *who* (the lock) and *once* (its own record for the
sigil), and signs a vote. It never sees assets, amounts, outputs or the
transaction graph; it keeps no ledger, orders nothing, and talks to no
other witness.

Per sigil an honest witness keeps a generation counter and at most one
binding per generation. It votes at most once per ``(sigil, generation)``.
A binding is only abandoned (generation bumped) when shown a death proof
that the bound transition can never be sealed. See docs/SPEC.md §5.
"""

from dataclasses import dataclass, field

from .charter import Registry, charter_hash, sign_charter
from .crypto import KeyPair
from .locks import evaluate
from .model import sigil_of, transition_id, vote_payload
from .proofs import proves_dead
from .stamps import StampMint


class Rejected(Exception):
    """The witness declined to vote."""


class Conflict(Rejected):
    """The sigil is already bound to a different transition at this generation."""

    def __init__(self, vote: dict | None):
        super().__init__("sigil bound to a different transition")
        self.vote = vote


CONTESTED = "!contested"


@dataclass
class Record:
    gen: int = 0
    tid: str | None = None          # bound transition at ``gen`` (or CONTESTED)
    header: dict | None = None
    vote: dict | None = None        # our vote for (sigil, gen, tid) under the current charter
    log: list = field(default_factory=list)    # evidence handed to successors on rotation
    votes: list = field(default_factory=list)  # every vote we ever cast on this sigil


def authorises(sigil: str, auth: dict) -> tuple[int, str] | None:
    """Validate an owner authorisation; return the (gen, tid) it binds, or None."""
    try:
        h = auth["header"]
        if sigil_of(auth) != sigil:
            return None
        gens = [g for s, g in h["inputs"] if s == sigil]
        sigils = [s for s, _ in h["inputs"]]
        if len(gens) != 1 or len(set(sigils)) != len(sigils):
            return None
        gen = gens[0]
        if not isinstance(gen, int) or isinstance(gen, bool) or gen < 0:
            return None
        tid = transition_id(h)
        if not evaluate(auth["lock"], auth["unlock"], sigil, tid, None):
            return None
        return gen, tid
    except (KeyError, TypeError, ValueError):
        return None


class Witness:
    def __init__(self, kp: KeyPair, registry: Registry, clock, *, stamp_mint: StampMint | None = None):
        self.kp = kp
        self.pk = kp.pk
        self.registry = registry
        self.clock = clock
        self.stamps = stamp_mint
        self.cid: str | None = None
        self.version: int | None = None
        self.frozen = False
        self.records: dict[str, Record] = {}

    # ------------------------------------------------------------ membership

    def join(self, cid: str, version: int) -> None:
        charter = self.registry.charter(cid, version)
        if charter is None or self.pk not in charter["witnesses"]:
            raise ValueError("not a member of this charter")
        self.cid, self.version = cid, version

    def _vote(self, sigil: str, gen: int, tid: str) -> dict:
        v = {
            "constellation": self.cid, "version": self.version, "witness": self.pk,
            "sigil": sigil, "gen": gen, "tid": tid, "time": int(self.clock()),
        }
        v["sig"] = self.kp.sign("vote", vote_payload(v))
        return v

    # ----------------------------------------------------------------- spend

    def spend(self, req: dict) -> dict:
        """Vote to bind ``req["sigil"]`` to the transition whose header is given.

        ``req`` carries: sigil, header, home, lock, salt, unlock, [stamp].
        """
        if self.cid is None or self.frozen:
            raise Rejected("witness not active")
        if self.stamps is not None and not self.stamps.redeem(req.get("stamp")):
            raise Rejected("missing or spent stamp")
        sigil = req.get("sigil")
        if req.get("home") != self.cid:
            raise Rejected("sigil does not live here")
        auth = {k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}
        bound = authorises(sigil, auth)
        if bound is None:
            raise Rejected("malformed request or lock not satisfied")
        gen, tid = bound
        # Time conditions are checked against our own clock: the quorum
        # that seals a time-locked spend therefore attests to the time.
        if not evaluate(auth["lock"], auth["unlock"], sigil, tid, int(self.clock())):
            raise Rejected("lock not satisfied now")

        rec = self.records.setdefault(sigil, Record())
        if gen < rec.gen:
            raise Rejected("stale generation")
        if gen > rec.gen:
            if rec.tid is not None:
                raise Rejected("bound at an earlier generation; release it first")
            rec.gen = gen  # we never voted at the skipped generations: abstaining is safe
        if rec.tid is None:
            rec.tid, rec.header = tid, auth["header"]
            rec.log.append({"kind": "bind", "gen": gen, "auth": auth})
        if rec.tid != tid:
            raise Conflict(rec.vote)
        if rec.vote is None:
            rec.vote = self._vote(sigil, gen, tid)
            rec.votes.append(rec.vote)
        return rec.vote

    # --------------------------------------------------------------- release

    def release(self, sigil: str, proof: dict) -> int:
        """Abandon the current binding if ``proof`` shows it can never be sealed.

        Returns the new generation. Releasing is what keeps an honest
        participant's parcel from being stuck when a counter-party in a
        multi-input transition equivocates on *their* input.
        """
        if self.cid is None or self.frozen:
            raise Rejected("witness not active")
        rec = self.records.get(sigil)
        if rec is None or rec.tid is None or rec.tid == CONTESTED:
            raise Rejected("nothing to release")
        if not proves_dead(rec.header, rec.tid, proof, self.registry):
            raise Rejected("invalid death proof")
        rec.log.append({"kind": "release", "gen": rec.gen, "tid": rec.tid, "header": rec.header, "proof": proof})
        rec.gen += 1
        rec.tid = rec.header = rec.vote = None
        return rec.gen

    # ----------------------------------------------------------------- query

    def status(self, sigil: str) -> dict:
        rec = self.records.get(sigil)
        if rec is None:
            return {"gen": 0, "tid": None, "votes": []}
        return {"gen": rec.gen, "tid": rec.tid, "votes": list(rec.votes)}

    def sell_stamp(self, blinded: int) -> int:
        if self.stamps is None:
            raise Rejected("this witness does not sell stamps")
        return self.stamps.sign_blinded(blinded)

    # -------------------------------------------------------------- rotation

    def freeze(self, next_charter: dict) -> tuple[str, dict]:
        """Stop voting forever and hand over evidence for the next charter.

        Returns our signature on the next charter and our evidence log.
        """
        if self.cid is None:
            raise Rejected("witness not active")
        if next_charter["prev"] != charter_hash(self.registry.charter(self.cid, self.version)):
            raise Rejected("charter does not extend ours")
        self.frozen = True
        return sign_charter(self.kp, next_charter), {s: list(r.log) for s, r in self.records.items()}

    def adopt(self, cid: str, version: int, snapshots: list) -> None:
        """Join a new charter version, inheriting predecessors' bindings.

        Only verifiable evidence is accepted: bindings must carry a valid
        owner authorisation and releases a valid death proof, so a lying
        predecessor can omit evidence (covered by the union) but never
        invent it.
        """
        self.join(cid, version)
        evidence: dict[str, list] = {}
        for snap in snapshots:
            for sigil, log in snap.items():
                evidence.setdefault(sigil, []).extend(log)
        for sigil, log in evidence.items():
            binds: dict[tuple, dict] = {}   # (gen, tid) -> header
            dead: set[str] = set()          # tids proven unsealable
            floor = 0                       # lowest generation still usable
            for e in log:
                if e.get("kind") == "bind":
                    b = authorises(sigil, e.get("auth", {}))
                    if b is not None:
                        binds[b] = e["auth"]["header"]
                elif e.get("kind") == "release":
                    h, t = e.get("header"), e.get("tid")
                    try:
                        if transition_id(h) == t and proves_dead(h, t, e.get("proof"), self.registry):
                            dead.add(t)
                    except (KeyError, TypeError, ValueError):
                        pass
            for (g, t) in binds:
                floor = max(floor, g + 1 if t in dead else g)
            # A death proof is a timeless fact about a transition, so it
            # retires that binding wherever it was reported.
            alive = {(g, t): h for (g, t), h in binds.items() if t not in dead}
            rec = Record(gen=floor, log=log)
            if len(alive) == 1:
                ((g, t), h), = alive.items()
                rec.gen, rec.tid, rec.header = g, t, h
            elif len(alive) > 1:
                rec.tid = CONTESTED  # the owner signed two live spends before rotation
            self.records[sigil] = rec
