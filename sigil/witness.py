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

With a ``store`` (``sigil.store.WitnessStore``) every state change is made
durable *before* the witness answers, and a restarted witness reloads it,
so a crash can never make it forget a vote and equivocate.
"""

from dataclasses import asdict, dataclass, field

from .charter import (MAX_CHARTER_BYTES, Registry, charter_body, charter_hash, checkpoint_hash, quorum, sign_charter,
                      valid_checkpoint_set)
from .crypto import KeyPair
from .encoding import canonical
from .locks import evaluate
from .model import heartbeat_payload, sigil_of, transition_id, vote_payload
from .proofs import acked_by, parse_settlement, proves_dead, unverifiable_death, verify_seal, verify_settlement, verify_vote
from .stamps import StampMint
from .store import WitnessStore, charter_entries, restore_charters


class Rejected(Exception):
    """The witness declined to vote."""


class Conflict(Rejected):
    """The sigil is already bound to a different transition at this generation."""

    def __init__(self, vote: dict | None):
        super().__init__("sigil bound to a different transition")
        self.vote = vote


CONTESTED = "!contested"

# What one request can make a witness store (SPEC §5.1, §5.2). Each refusal is a
# clean Rejected that changes nothing: declining to vote or to release is
# abstention, which is always safe, so these bound storage without touching safety.
MAX_AUTH_BYTES = 32 << 10    # enc({home, lock, salt, unlock, header}) of a SPEND
MAX_PROOF_BYTES = 128 << 10  # enc(proof) of a RELEASE (a death proof for 128 witnesses fits)
MAX_GEN = 16                 # a sigil is newly bound only below this generation (so at most 16 times)
MAX_SETTLE_BYTES = 512 << 10  # enc(settlement) of a SETTLE (SPEC §5.7)

# Record.settled (SPEC §5, §5.7).
UNSETTLED, SETTLED, CHECKPOINTED = 0, 1, 2
MAX_UNVERIFIED_RELEASES = 4  # per tid, releases a standby member keeps that it cannot verify (§5.5)
MAX_GEN_VALUE = 1 << 62      # no authorisation names a generation at or above this (SPEC §5.1 step 3)


def _encoding(x):
    """``enc(x)``, or a key unique to ``x`` if it has none (in-process callers only)."""
    try:
        return canonical(x)
    except (ValueError, TypeError, RecursionError):
        return id(x)


def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def _too_big(x, limit: int) -> bool | None:
    """Is ``enc(x)`` longer than ``limit`` bytes? None if ``x`` has no canonical encoding."""
    try:
        return len(canonical(x)) > limit
    except (ValueError, TypeError, RecursionError):
        return None


@dataclass
class Record:
    gen: int = 0
    tid: str | None = None          # bound transition at ``gen`` (or CONTESTED)
    header: dict | None = None
    vote: dict | None = None        # our vote for (sigil, gen, tid) under the current charter
    log: list = field(default_factory=list)    # evidence handed to successors on rotation
    votes: list = field(default_factory=list)  # every vote we ever cast on this sigil
    abstain: bool = False           # our key already voted another tid at ``gen``: never vote here
    candidates: list = field(default_factory=list)  # CONTESTED: live [gen, tid, header] still to be proven dead
    # SETTLED: a certificate showed (gen, tid) complete; CHECKPOINTED: in our charter's
    # checkpoint set (no log). Either way the record never votes or releases again.
    settled: int = UNSETTLED

    def copy(self) -> "Record":
        """A working copy; log entries are never mutated, so the lists are copied shallowly."""
        return Record(self.gen, self.tid, self.header, self.vote, list(self.log), list(self.votes),
                      self.abstain, list(self.candidates), self.settled)


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
        # Below 2**62, as in the Rust witness: both must accept exactly the same evidence.
        if not isinstance(gen, int) or isinstance(gen, bool) or not 0 <= gen < MAX_GEN_VALUE:
            return None
        exp = auth["unlock"].get("expires")
        if not isinstance(exp, int) or isinstance(exp, bool):
            return None
        tid = transition_id(h)
        if not evaluate(auth["lock"], auth["unlock"], sigil, tid, None):
            return None
        return gen, tid
    except (KeyError, TypeError, ValueError, AttributeError):  # e.g. a non-object unlock
        return None


class Evidence:
    """What a handover log of one sigil proves (SPEC §5.4), as ADOPT and STANDBY read it."""

    def __init__(self):
        self.binds: dict[tuple, dict] = {}   # (gen, tid) -> header, of verified bind entries
        self.dead: set[str] = set()          # tids whose death proof verified
        self.sealed: set[tuple] = set()      # (gen, tid) with a verified seal
        self.votes: list = []                # verified votes of this constellation on the sigil
        self.log: list = []                  # verified evidence bearing on a binding, in order
        self.kept: list = []                 # ``log`` plus the verified vote entries, in order


def classify_evidence(sigil: str, log: list, cid: str, registry, voter: str | None = None,
                      members=None) -> Evidence:
    """Verify each entry of a (deduplicated) handover log of ``sigil`` for constellation ``cid``.

    Bind entries count if their authorisation passes §5.1 step 3 (with no clock); release
    entries if their death proof verifies against their header; seal entries if the seal
    verifies for this sigil and constellation; vote entries if the vote is a valid vote of
    this constellation on this sigil. Releases and seals only ever bear on bound transactions
    (an honest witness logs one only for a transaction it bound), so ``log`` keeps them only
    for a transaction bound in this evidence; everything else is junk anyone could add.
    With ``voter``, only that key's votes are checked and kept (ADOPT needs only its own).

    Without ``voter`` (STANDBY) ``kept`` also holds, for a binding it keeps and no verified release
    of, up to ``MAX_UNVERIFIED_RELEASES`` releases whose death proof passes every check that needs
    no charter but names a charter version this member does not know (``unverifiable_death``: a
    later adopter that knows it can verify it), within ``MAX_PROOF_BYTES``; and a vote
    only if its sigil has a kept binding or its signer is in ``members`` (the version handed
    over, so a re-used key's own votes travel): votes on made-up sigils are padding.
    """
    ev = Evidence()
    releases, seals, votes, unknown = [], [], [], []
    for e in log:
        kind = e.get("kind")
        if kind == "vote":
            v = e.get("vote")
            try:
                # A vote counts only if signed by a member of the version it names (or, for
                # ADOPT, by our own key): anyone can mint keys and sign votes with them.
                if ((v["witness"] == voter if voter is not None else
                     (_is_int(v["version"]) and v["witness"] in ((registry.charter(cid, v["version"]) or {})
                                                                  .get("witnesses", ()))))
                        and v["sigil"] == sigil and v["constellation"] == cid and _is_int(v["gen"])
                        and isinstance(v["tid"], str) and verify_vote(v)):
                    ev.votes.append(v)
                    votes.append(e)
            except (KeyError, TypeError):
                pass
        elif kind == "bind":
            b = authorises(sigil, e.get("auth", {}))
            if b is not None:
                ev.binds[b] = e["auth"]["header"]
                ev.log.append(e)
        elif kind == "seal":
            sl = e.get("seal")
            try:
                if sl["sigil"] == sigil and sl["constellation"] == cid and verify_seal(sl, registry):
                    ev.sealed.add((sl["gen"], sl["tid"]))
                    seals.append(((sl["gen"], sl["tid"]), e))
            except (KeyError, TypeError):
                pass
        elif kind == "release":
            h, t = e.get("header"), e.get("tid")
            try:
                if transition_id(h) == t and proves_dead(h, t, e.get("proof"), registry):
                    ev.dead.add(t)
                    releases.append((t, e))
                elif (voter is None and transition_id(h) == t
                      and unverifiable_death(h, t, e.get("proof"), registry)
                      and _too_big(e.get("proof"), MAX_PROOF_BYTES) is False):
                    unknown.append((t, e))
            except (KeyError, TypeError, ValueError):
                pass
    bound_tids = {t for (_g, t) in ev.binds}
    useful = {id(e) for e in ev.log}
    useful |= {id(e) for t, e in releases if t in bound_tids}
    useful |= {id(e) for b, e in seals if b in ev.binds}
    ev.log = [e for e in log if id(e) in useful]
    bound_sigil = bool(ev.binds)
    useful |= {id(e) for e in votes if voter is not None or bound_sigil or e["vote"]["witness"] in (members or ())}
    count: dict = {}
    for t, e in unknown:
        if t in bound_tids and t not in ev.dead and count.get(t, 0) < MAX_UNVERIFIED_RELEASES:
            count[t] = count.get(t, 0) + 1
            useful.add(id(e))
    ev.kept = [e for e in log if id(e) in useful]
    return ev


class Witness:
    def __init__(self, kp: KeyPair, registry: Registry, clock, *, stamp_mint: StampMint | None = None,
                 store: WitnessStore | None = None):
        self.kp = kp
        self.pk = kp.pk
        self.registry = registry
        self.clock = clock
        self.stamps = stamp_mint
        self.cid: str | None = None
        self.version: int | None = None
        self.frozen = False
        self.frozen_for: str | None = None  # hash of the one successor charter we froze for
        self.records: dict[str, Record] = {}
        self._charters_saved: dict[str, int] = {}  # cid -> chain length the store holds
        self._charters_keep = set(registry.ids())  # constellations the registry file names
        self.store = store
        if store is not None:
            self._restore()

    # ------------------------------------------------------------ durability

    def _restore(self) -> None:
        state = self.store.load()
        if state["pk"] is None:
            self.store.append([("pk", "", self.pk)])
        elif state["pk"] != self.pk:
            raise ValueError("store belongs to a different witness key")
        # Charter chains learned before the restart: the registry file may predate them.
        self._charters_saved = restore_charters(self.registry, state.get("charters", {}))
        if state["member"] is not None:
            self.cid, self.version = state["member"]
        # Stores written before successor binding hold ``true``: the successor
        # is unknown, so any further freeze is refused.
        self.frozen = bool(state["frozen"])
        self.frozen_for = state["frozen"] if isinstance(state["frozen"], str) else None
        self.records = {s: Record(**r) for s, r in state["records"].items()}
        if self.stamps is not None:
            self.stamps.mark_redeemed(state["stamps"])

    def _persist(self, *entries: tuple[str, str, object]) -> None:
        """Make ``entries`` durable (no-op without a store). Callers mutate state only afterwards."""
        if self.store is not None:
            self.store.append(list(entries))

    def remember_charters(self) -> None:
        """Persist every charter chain our registry learned (by gossip or ADOPT) that the
        store does not hold yet, so a restart from an older registry file still knows them."""
        if self.store is not None:
            saved = dict(self._charters_saved)
            entries = charter_entries(self.registry, saved, self._charters_keep)
            if entries:
                self._persist(*entries)
            self._charters_saved = saved

    @staticmethod
    def _format_entry() -> list:
        """Written with every settled or checkpointed record: a store holding one must not be
        opened by a version that cannot read it (a Rust binary from before compaction refuses
        an unknown entry kind; a Python one fails on the ``settled`` field), since a checkpointed
        record has no log and an old version would hand it over as nothing."""
        return [("format", "", 2)]

    @staticmethod
    def _rec(sigil: str, rec: Record) -> tuple[str, str, dict]:
        return ("record", sigil, asdict(rec))

    # ------------------------------------------------------------ membership

    def _check_member(self, cid: str, version: int) -> None:
        charter = self.registry.charter(cid, version)
        if charter is None or self.pk not in charter["witnesses"]:
            raise ValueError("not a member of this charter")

    def join(self, cid: str, version: int) -> None:
        self._check_member(cid, version)
        self._persist(("member", "", [cid, version]))
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
        if not isinstance(req, dict):
            raise Rejected("malformed request")
        if self.stamps is not None:
            if not self.stamps.redeem(req.get("stamp")):
                raise Rejected("missing or spent stamp")
            self._persist(("stamp", req["stamp"]["serial"], True))
        sigil = req.get("sigil")
        if req.get("home") != self.cid:
            raise Rejected("sigil does not live here")
        auth = {k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}
        big = _too_big(auth, MAX_AUTH_BYTES)
        if big:
            raise Rejected("authorisation too large")
        bound = authorises(sigil, auth) if big is not None else None
        if bound is None:
            raise Rejected("malformed request or lock not satisfied")
        gen, tid = bound
        # Time conditions are checked against our own clock: the quorum
        # that seals a time-locked spend therefore attests to the time.
        if not evaluate(auth["lock"], auth["unlock"], sigil, tid, int(self.clock())):
            raise Rejected("lock not satisfied now")

        old = self.records.get(sigil)
        if old is not None and old.settled:
            # Its transition is complete (SPEC §5.7): never a new vote, only the one we hold.
            if (old.gen, old.tid) == (gen, tid) and old.vote is not None:
                return old.vote
            if old.tid != tid:
                raise Conflict(old.vote)
            raise Rejected("sigil consumed: its transition is complete")
        rec = old.copy() if old is not None else Record()
        if gen < rec.gen:
            raise Rejected("stale generation")
        if gen > rec.gen:
            if rec.tid is not None:
                raise Rejected("bound at an earlier generation; release it first")
            rec.gen = gen  # we never voted at the skipped generations: abstaining is safe
        if rec.tid is None:
            # Never *newly* bind on an expired authorisation: once it has
            # expired, an owner can safely conclude a failed spend is dead.
            if int(self.clock()) > auth["unlock"]["expires"]:
                raise Rejected("authorisation expired")
            # Each new binding is at a higher generation than the last (a release
            # moves past it), so this bounds the bindings one sigil can collect. It
            # reads our own counter, not the log: ADOPT evidence from a Byzantine
            # predecessor can hold junk entries, but cannot raise a generation
            # without the owner's signature or a valid death proof.
            if gen >= MAX_GEN:
                raise Rejected("generation limit reached for this sigil")
            rec.tid, rec.header = tid, auth["header"]
            rec.log.append({"kind": "bind", "gen": gen, "auth": auth})
        if rec.tid != tid:
            raise Conflict(rec.vote)
        if rec.vote is None and rec.abstain:
            raise Rejected("this key already voted for another transition at this generation")
        if rec.vote is None:
            # Mirror before vote (SPEC §5.5): a version with a successor committee
            # never creates a vote that a committee quorum has not stored first, so
            # any succession inherits it. Nothing is persisted on refusal. Without
            # our own charter (a registry older than our store) we cannot tell
            # whether acks are needed, so we create no vote at all.
            if self.registry.charter(self.cid, self.version) is None:
                raise Rejected("own charter version unknown")
            committee = self.registry.committee(self.cid, self.version)
            if committee is not None and len(acked_by(req.get("mirror"), committee, self.cid, self.version,
                                                      sigil, gen, tid)) < quorum(len(committee)):
                raise Rejected("needs mirror acks from a quorum of the successor committee")
            rec.vote = self._vote(sigil, gen, tid)
            rec.votes.append(rec.vote)
        if rec != old:
            self._persist(self._rec(sigil, rec))  # durable before the vote leaves
            self.records[sigil] = rec
        return rec.vote

    # --------------------------------------------------------------- release

    def release(self, sigil: str, proof: dict) -> int:
        """Abandon the current binding if ``proof`` shows it can never be sealed.

        Returns the new generation. Releasing is what keeps an honest
        participant's parcel from being stuck when a counter-party in a
        multi-input transition equivocates on *their* input.

        A CONTESTED record drops each candidate that ``proof`` kills, and is
        released once none is left.
        """
        if self.cid is None or self.frozen:
            raise Rejected("witness not active")
        rec = self.records.get(sigil)
        if rec is None or rec.tid is None:
            raise Rejected("nothing to release")
        if rec.settled:
            raise Rejected("sigil consumed: its transition is complete")
        big = _too_big(proof, MAX_PROOF_BYTES)
        if big is not False:
            raise Rejected("death proof too large" if big else "invalid death proof")
        if rec.tid == CONTESTED:
            return self._release_contested(sigil, rec, proof)
        if not proves_dead(rec.header, rec.tid, proof, self.registry):
            raise Rejected("invalid death proof")
        rec = rec.copy()
        rec.log.append({"kind": "release", "gen": rec.gen, "tid": rec.tid, "header": rec.header, "proof": proof})
        rec.gen += 1
        rec.tid = rec.header = rec.vote = None
        rec.abstain = False
        self._persist(self._rec(sigil, rec))
        self.records[sigil] = rec
        return rec.gen

    def _release_contested(self, sigil: str, rec: Record, proof: dict) -> int:
        killed = [c for c in rec.candidates if proves_dead(c[2], c[1], proof, self.registry)]
        sealed = self._sealed_candidate(sigil, rec, proof, killed)
        if not killed and sealed is None:
            raise Rejected("invalid death proof")
        rec = rec.copy()
        for g, t, h in killed:
            rec.log.append({"kind": "release", "gen": g, "tid": t, "header": h, "proof": proof})
        rec.candidates = [c for c in rec.candidates if c not in killed]
        # We never vote while contested, so the generation can rise as each
        # candidate dies; once none is left we sit past all of them, unbound.
        rec.gen = max([rec.gen] + [g + 1 for g, _, _ in killed])
        if sealed is not None:
            # The one candidate left is sealed at its generation (by any version
            # of our home), so no other tid can ever be sealed there (SPEC §8
            # Lemma 1): bind to it. Voting it again creates no second seal.
            g, t, h = sealed
            rec.log.append({"kind": "seal", "gen": g, "tid": t, "seal": proof["seal"]})
            rec.gen, rec.tid, rec.header, rec.candidates = g, t, h, []
            rec.abstain = any(v["gen"] == g and v["tid"] != t for v in rec.votes)
        elif not rec.candidates:
            rec.tid = None
            if rec.votes:  # a re-used key skips every generation it voted at (abstention)
                rec.gen = max(rec.gen, max(v["gen"] for v in rec.votes) + 1)
        self._persist(self._rec(sigil, rec))
        self.records[sigil] = rec
        return rec.gen

    def _sealed_candidate(self, sigil: str, rec: Record, proof: dict, killed: list):
        """The candidate ``proof`` shows sealed, if it would be the only one left.

        Only when nothing at a higher generation has been passed over
        (``gen <= g + 1`` once the killed candidates are counted): binding
        back to ``g`` must not re-open a generation another candidate held.
        """
        try:
            if proof.get("kind") != "seal":
                return None
            seal = proof["seal"]
            left = [c for c in rec.candidates if c not in killed]
            if len(left) != 1:
                return None
            g, t, h = left[0]
            top = max([rec.gen] + [kg + 1 for kg, _, _ in killed])
            ok = (seal["sigil"] == sigil and seal["gen"] == g and seal["tid"] == t
                  and seal["constellation"] == self.cid and top <= g + 1
                  and all(v["gen"] <= g for v in rec.votes)  # never step back below our own votes
                  and verify_seal(seal, self.registry))
            return left[0] if ok else None
        except (KeyError, TypeError, AttributeError):
            return None

    # ------------------------------------------------------------ settlement

    def settle(self, cert) -> dict:
        """SETTLE (SPEC §5.7): ``cert`` shows a transition complete; settle our bindings to it.

        SETTLE never changes a binding. An input that lives here is settled only if we
        already hold it bound to exactly the certificate's transition at the
        certificate's generation (not contested, not released, not settled): from then
        on we never vote on that sigil again (except to hand back the vote we hold) and
        never release it. Every seal must come from the CURRENT charter version of its
        home as our registry knows it: retired keys (of our home or another) cannot make
        a transition look complete, so an honest owner's kill-switch recovery stays
        possible. The log is kept for the next handover until a checkpoint covers it.
        """
        if self.cid is None or self.frozen:
            raise Rejected("witness not active")
        big = _too_big(cert, MAX_SETTLE_BYTES)
        if big is not False:
            raise Rejected("settlement too large" if big else "invalid settlement certificate")
        parsed = parse_settlement(cert)
        if parsed is None:
            raise Rejected("invalid settlement certificate")
        tid, inputs = parsed
        mine = [(s, g) for s, g, home, _seal in inputs if home == self.cid]
        if not mine:
            raise Rejected("no input of this transition lives here")
        held = [(s, g) for s, g in mine if (r := self.records.get(s)) is not None and (r.gen, r.tid) == (g, tid)]
        if not held:
            raise Rejected("this witness holds no binding of this transition")
        for _s, _g, home, seal in inputs:
            cur = self.registry.latest(home)
            if cur is None or type(seal.get("version")) is not int or seal["version"] != cur["version"]:
                raise Rejected("a seal is not from its home's current charter version")
        if verify_settlement(cert, self.registry) is None:
            raise Rejected("invalid settlement certificate")
        changed = {}
        for s, g in held:
            rec = self.records[s]
            if rec.settled:
                continue
            rec = rec.copy()
            rec.settled = SETTLED
            changed[s] = rec
        if changed:
            self._persist(*self._format_entry(), *(self._rec(s, r) for s, r in changed.items()))
            self.records.update(changed)
        return {"settled": sorted(s for s, g in held)}

    def settled_records(self) -> dict:
        """SETTLED (SPEC §5.7): our settled and checkpointed records as ``[sigil, gen, tid]``."""
        out = {"settled": [], "checkpointed": []}
        for s in sorted(self.records):
            r = self.records[s]
            if r.settled == SETTLED:
                out["settled"].append([s, r.gen, r.tid])
            elif r.settled == CHECKPOINTED:
                out["checkpointed"].append([s, r.gen, r.tid])
        return out

    def _checkpoint_for(self, body: dict, entries) -> dict:
        """The checkpoint set ``entries`` of charter ``body`` as ``{sigil: (gen, tid)}``.

        Raises Rejected unless it matches the body's ``checkpoint`` hash (a body
        without one has the empty set).
        """
        ck = body.get("checkpoint")
        if ck is None:
            if entries not in (None, []):
                raise Rejected("this charter carries no checkpoint")
            return {}
        if not valid_checkpoint_set(entries) or checkpoint_hash(entries) != ck:
            raise Rejected("checkpoint set does not match the charter")
        return {e[0]: (e[1], e[2]) for e in entries}

    # ----------------------------------------------------------------- query

    def status(self, sigil: str) -> dict:
        rec = self.records.get(sigil)  # an unhashable sigil is a bad request, first
        # A witness that has not joined (awaiting ADOPT) knows nothing yet: "unbound" from it
        # would read as an answer from a current member (SPEC §4 rule 3), so it answers nothing.
        if self.cid is None:
            raise Rejected("witness not active")
        if rec is None:
            return {"gen": 0, "tid": None, "votes": []}
        return {"gen": rec.gen, "tid": rec.tid, "votes": list(rec.votes)}

    def sell_stamp(self, blinded: int) -> int:
        if self.stamps is None:
            raise Rejected("this witness does not sell stamps")
        return self.stamps.sign_blinded(blinded)

    def heartbeat(self, challenge) -> dict:
        """Show a standby member that this witness is alive and voting (SPEC §5.5).

        Only an active, unfrozen witness answers: a frozen one will never vote again.
        The challenge is the standby member's own fresh string, so an answer cannot
        be replayed later to fake liveness.
        """
        if self.cid is None or self.frozen:
            raise Rejected("witness not active")
        if not isinstance(challenge, str) or not 0 < len(challenge) <= 128:
            raise Rejected("challenge must be a string of 1 to 128 characters")
        h = {"constellation": self.cid, "version": self.version, "witness": self.pk, "challenge": challenge}
        h["sig"] = self.kp.sign("heartbeat", heartbeat_payload(h))
        return h

    # -------------------------------------------------------------- rotation

    def freeze(self, next_charter: dict, checkpoint: list | None = None) -> tuple[str, dict]:
        """Stop voting forever and hand over evidence for the next charter.

        Returns our signature on the next charter and our evidence log. If the
        charter carries a checkpoint, ``checkpoint`` is its set: we freeze only if
        every entry matches a record we hold settled and every record we hold
        checkpointed is in it (SPEC §5.7), and the snapshot omits those sigils.
        """
        if self.cid is None:
            raise Rejected("witness not active")
        cur = self.registry.charter(self.cid, self.version)
        if next_charter["prev"] != charter_hash(cur):  # not an object, or no prev: bad_request
            raise Rejected("charter does not extend ours")
        # Freezing is irreversible, so only for a body that can become a valid version v+1:
        # the same name, the next version, a well-formed witness list and successor clause
        # (charter_body applies the size and uniqueness rules) and a charter within the cap.
        try:
            well_formed = (next_charter == charter_body(next_charter["name"], next_charter["version"],
                                                        next_charter["witnesses"], next_charter["prev"],
                                                        next_charter.get("successor"), next_charter.get("checkpoint"))
                           and all(isinstance(k, str) for k in next_charter["witnesses"])
                           and len(canonical({"body": next_charter, "sigs": {}})) <= MAX_CHARTER_BYTES)
        except (KeyError, TypeError, ValueError, AttributeError):
            well_formed = False
        if (not well_formed or next_charter["name"] != cur["name"] or not isinstance(next_charter["version"], int)
                or isinstance(next_charter["version"], bool) or next_charter["version"] != self.version + 1):
            raise Rejected("not a valid next version of our charter")
        ck = self._checkpoint_for(next_charter, checkpoint)
        for s, (g, t) in ck.items():
            r = self.records.get(s)
            if r is None or not r.settled or (r.gen, r.tid) != (g, t):
                raise Rejected("checkpoint names a binding this witness does not hold settled")
        if any(r.settled == CHECKPOINTED and s not in ck for s, r in self.records.items()):
            # The extension rule: a checkpointed record has no log to hand over.
            raise Rejected("checkpoint drops a sigil of our own checkpoint")
        # We sign exactly one successor: signing two lets a quorum of honest
        # witnesses certify two conflicting version v+1 charters (a fork).
        h = charter_hash(next_charter)
        if self.frozen and self.frozen_for != h:
            raise Rejected("already frozen for a different successor charter")
        if not self.frozen:
            self._persist(("frozen", "", h))
            self.frozen, self.frozen_for = True, h
        # Our signed votes travel with the evidence so that, if our key is
        # re-used in the next charter, we never vote a different transition
        # at a (sigil, generation) where we already voted.
        snapshot = {s: list(r.log) + [{"kind": "vote", "vote": v} for v in r.votes]
                    for s, r in self.records.items() if s not in ck}
        if self.pk in next_charter["witnesses"]:
            # A re-used key keeps its own vote for a checkpointed binding (STATUS still shows it).
            for s in ck:
                r = self.records[s]
                mine = [{"kind": "vote", "vote": v} for v in r.votes if (v["gen"], v["tid"]) == (r.gen, r.tid)]
                if mine:
                    snapshot[s] = mine
        return sign_charter(self.kp, next_charter), snapshot

    def adopt(self, cid: str, version: int, snapshots: list, checkpoint: list | None = None) -> None:
        """Join a new charter version, inheriting predecessors' bindings.

        If the new charter carries a checkpoint, ``checkpoint`` must be its set
        (SPEC §5.7): each entry becomes a checkpointed record, with no log, and
        whatever the snapshots say about those sigils is ignored.

        Only verifiable evidence is accepted: bindings must carry a valid
        owner authorisation and releases a valid death proof, so a lying
        predecessor can omit evidence (covered by the union) but never
        invent it. Snapshots arrive from untrusted predecessors (over the
        wire, ``/v0/adopt``), so malformed parts are skipped like any other
        unverifiable evidence: a snapshot that is not an object, a log that
        is not a list, and log entries that are not objects.

        The new record's log keeps only the evidence that verified and bears
        on a binding: bind entries with a valid authorisation, and release and
        seal entries that verify for a transaction bound in this evidence.
        Everything else (junk, other keys' votes, releases of transactions
        nobody bound) is dropped, so a Byzantine predecessor cannot pad a
        sigil's log for every later version.
        """
        self._check_member(cid, version)
        ck = self._checkpoint_for(self.registry.charter(cid, version), checkpoint)
        records: dict[str, Record] = {}
        evidence: dict[str, list] = {}
        seen: dict[str, set] = {}  # per sigil, the encodings of the entries kept so far
        for snap in snapshots:
            if not isinstance(snap, dict):
                continue
            for sigil, log in snap.items():
                if not isinstance(log, list):
                    continue
                # The evidence is a set: honest predecessors hand over the same
                # entries, and without dropping repeats each rotation would
                # multiply a sigil's log by the number of signers.
                kept, have = evidence.setdefault(sigil, []), seen.setdefault(sigil, set())
                for e in log:
                    if isinstance(e, dict):
                        k = _encoding(e)
                        if k not in have:
                            have.add(k)
                            kept.append(e)
        for sigil, (g, t) in ck.items():
            # Our own vote for exactly this binding, if our key cast one (a re-used key).
            prior = self.records.get(sigil)
            mine = [v for v in (prior.votes if prior else []) if v["gen"] == g and v["tid"] == t]
            for e in evidence.get(sigil, []):
                v = e.get("vote") if e.get("kind") == "vote" else None
                try:
                    if (not mine and v["witness"] == self.pk and v["sigil"] == sigil and v["constellation"] == cid
                            and v["gen"] == g and v["tid"] == t and verify_vote(v)):
                        mine = [v]
                except (KeyError, TypeError):
                    pass
            records[sigil] = Record(gen=g, tid=t, vote=mine[0] if mine else None, votes=mine[:1],
                                    settled=CHECKPOINTED)
        for sigil, log in evidence.items():
            if sigil in ck:
                continue
            prior = self.records.get(sigil)
            ev = classify_evidence(sigil, log, cid, self.registry, voter=self.pk)
            own = {(v["gen"], v["tid"]): v for v in (prior.votes if prior else [])}  # votes our key cast
            for v in ev.votes:
                own[(v["gen"], v["tid"])] = v
            binds, dead, sealed = ev.binds, ev.dead, ev.sealed
            if not ev.log and not own and prior is None:
                continue  # nothing verifiable bears on this sigil: no record (no padding carried)
            floor = 0                       # lowest generation still usable
            for (g, t) in binds:
                floor = max(floor, g + 1 if t in dead else g)
            # A death proof is a timeless fact about a transition, so it
            # retires that binding wherever it was reported.
            alive = {(g, t): h for (g, t), h in binds.items() if t not in dead}
            rec = Record(gen=floor, log=list(ev.log), votes=list(own.values()))
            lone = False
            if len(alive) == 1:
                (g, t), = alive
                others = [g2 for (g2, t2) in binds if (g2, t2) != (g, t)]
                top = all(g2 <= g for g2 in others) if (g, t) in sealed else all(g2 < g for g2 in others)
                lone = top and all(og <= g for og, _ in own)
            if lone:
                ((g, t), h), = alive.items()
                rec.gen, rec.tid, rec.header = g, t, h
                # Inheriting a binding never makes our key sign a second tid at g.
                rec.abstain = any(og == g and ot != t for og, ot in own)
            elif not alive and own:
                rec.gen = max(floor, max(og for og, _ in own) + 1)  # skipping our own gens is abstention
            elif alive:
                # Contested: never vote; released once every candidate is proven dead.
                rec.tid = CONTESTED
                rec.candidates = [[g, t, h] for (g, t), h in sorted(alive.items(), key=lambda kv: kv[0])]
            records[sigil] = rec
        # Membership and inherited records land in one atomic batch: a crash
        # must never leave us active but missing a binding. The charter chains we
        # know (our new version's among them) land with it: a restart from an older
        # registry file must still know the version we are a member of.
        saved = dict(self._charters_saved)
        charters = []
        if self.store is not None and cid in self._charters_keep:
            charters = [("charter", cid, self.registry.chain(cid))]  # always our own chain
            saved[cid] = len(charters[0][2])
        self._persist(*charters, ("member", "", [cid, version]), *(self._format_entry() if ck else []),
                      *(self._rec(s, r) for s, r in records.items()))
        self._charters_saved = saved
        self.cid, self.version = cid, version
        self.records.update(records)
