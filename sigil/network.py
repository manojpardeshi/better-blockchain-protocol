"""An in-process network of constellations, for simulation and tests.

Witnesses are independent objects; the "network" is just the address book
plus fault injection (crashed witnesses). Nothing here is trusted by the
protocol: wallets verify every vote and seal they receive.

A constellation may have a successor committee (SPEC §5.5): ``committees[cid]``
holds its standby members, and ``succeed`` drives a dead-man takeover.
"""

from .charter import Registry, charter_body, charter_hash, constellation_id, quorum, successor_clause
from .crypto import KeyPair
from .stamps import StampMint
from .succession import Standby
from .witness import Rejected, Witness


class SimClock:
    def __init__(self, t: int = 1_700_000_000):
        self.t = t

    def __call__(self) -> int:
        return self.t

    def advance(self, dt: int) -> None:
        self.t += dt


class Network:
    def __init__(self, clock=None):
        self.clock = clock or SimClock()
        self.registry = Registry()          # public charter directory (gossiped in reality)
        self.members: dict[str, list[Witness]] = {}
        self.committees: dict[str, list[Standby]] = {}
        self.retired: dict[str, list[Witness]] = {}  # members of earlier versions (they may still be alive)
        self.retired_committees: dict[str, list[Standby]] = {}  # standby members of earlier versions
        self.down: set[str] = set()

    def create_constellation(self, name: str, n: int = 4, *, witness_cls=Witness,
                             byzantine: dict | None = None, stamps: bool = False,
                             stamp_bits: int = 1024, successor: dict | None = None) -> str:
        """Create a constellation of ``n`` witnesses.

        ``byzantine`` maps witness index -> Witness subclass to use instead.
        ``successor`` = ``{"n": k, "dead_man": seconds}`` (or ``"keys": [KeyPair]``
        instead of ``n``) gives version 0 a successor committee of standby members.
        """
        keys = [KeyPair.generate() for _ in range(n)]
        ckeys, succ = self._committee_keys(successor)
        body = charter_body(name, 0, [k.pk for k in keys], None, succ)
        cid = constellation_id(body)
        self.registry.add_chain(cid, [{"body": body, "sigs": {}}])
        ws = []
        for i, kp in enumerate(keys):
            cls = (byzantine or {}).get(i, witness_cls)
            w = cls(kp, self.registry, self.clock, stamp_mint=StampMint(stamp_bits) if stamps else None)
            w.join(cid, 0)
            ws.append(w)
        self.members[cid] = ws
        self.committees[cid] = self._stand_by(cid, 0, ckeys, [])
        return cid

    @staticmethod
    def _committee_keys(successor: dict | None) -> tuple[list, dict | None]:
        if successor is None:
            return [], None
        ckeys = successor.get("keys") or [KeyPair.generate() for _ in range(successor["n"])]
        return ckeys, successor_clause([k.pk for k in ckeys], successor["dead_man"])

    def _stand_by(self, cid: str, version: int, ckeys: list, snapshots: list,
                  standby_cls=Standby) -> list:
        out = []
        for kp in ckeys:
            m = standby_cls(kp, self.registry, self.clock)
            m.enter(cid, version, snapshots)
            out.append(m)
        return out

    def witnesses(self, cid: str) -> list[Witness]:
        return [w for w in self.members.get(cid, []) if w.pk not in self.down]

    def all_witnesses(self, cid: str) -> list[Witness]:
        return list(self.members.get(cid, []))

    def committee(self, cid: str) -> list[Standby]:
        """The reachable standby members of ``cid``'s current version (SPEC §5.5)."""
        return [m for m in self.committees.get(cid, []) if m.pk not in self.down]

    def probe(self, cid: str) -> None:
        """Every reachable standby member challenges every reachable member (heartbeats)."""
        for m in self.committee(cid):
            m.probe(self.witnesses(cid))

    def rotate(self, cid: str, new_keys: list[KeyPair], witness_cls=Witness, *,
               successor: dict | None = None) -> int:
        """Replace a constellation's membership; returns the new version.

        Old members freeze and sign the new charter; new members adopt the
        union of the evidence handed over by the quorum that signed. If the
        current version has a successor committee, the committee must sign too
        (SPEC §5.5): its members get the members' signatures as the request,
        fence, and hand over their mirror logs as well. ``successor`` gives the
        new version a committee (``{"n" | "keys", "dead_man"}``).
        """
        chain = self.registry.chain(cid)
        cur = chain[-1]["body"]
        ckeys, succ = self._committee_keys(successor)
        nxt = charter_body(cur["name"], cur["version"] + 1, [k.pk for k in new_keys], charter_hash(cur), succ)
        sigs, snapshots = {}, []
        for w in self.witnesses(cid):
            try:
                sig, snap = w.freeze(nxt)
            except Rejected:
                continue
            sigs[w.pk] = sig
            snapshots.append(snap)
        if len(sigs) < quorum(len(cur["witnesses"])):
            raise RuntimeError("not enough live witnesses to rotate")
        frozen = set(sigs)
        if cur.get("successor") is not None:
            csigs = self._committee_signatures(cid, nxt, dict(sigs), snapshots)
            if len(csigs) < quorum(len(cur["successor"]["committee"])):
                raise RuntimeError("not enough live standby members to sign the rotation")
            sigs.update(csigs)
        return self._install(cid, chain, nxt, sigs, snapshots, new_keys, ckeys, witness_cls, frozen)

    def succeed(self, cid: str, new_keys: list[KeyPair], witness_cls=Witness, *,
                successor: dict | None = None) -> int:
        """Dead-man takeover (SPEC §5.5): the committee signs the next version alone.

        Each reachable standby member signs only if the dead-man condition holds for
        it; with a quorum of signatures the new members adopt from the standby
        members' mirror logs. Raises ``RuntimeError`` without a quorum.
        """
        chain = self.registry.chain(cid)
        cur = chain[-1]["body"]
        if cur.get("successor") is None:
            raise ValueError("this version names no successor committee")
        ckeys, succ = self._committee_keys(successor)
        nxt = charter_body(cur["name"], cur["version"] + 1, [k.pk for k in new_keys], charter_hash(cur), succ)
        # Two phases (as RemoteNetwork.succeed): ask first, so a minority never fences alone.
        if sum(1 for m in self.committee(cid) if m.dead()) < quorum(len(cur["successor"]["committee"])):
            raise RuntimeError("not enough standby members agree the version is dead")
        snapshots: list = []
        sigs = self._committee_signatures(cid, nxt, {}, snapshots)
        if len(sigs) < quorum(len(cur["successor"]["committee"])):
            raise RuntimeError("not enough standby members agree the version is dead")
        return self._install(cid, chain, nxt, sigs, snapshots, new_keys, ckeys, witness_cls)

    def _committee_signatures(self, cid: str, nxt: dict, member_sigs: dict, snapshots: list) -> dict:
        out = {}
        for m in self.committee(cid):
            try:
                sig, snap = m.succeed(nxt, member_sigs)
            except Rejected:
                continue
            out[m.pk] = sig
            snapshots.append(snap)
        return out

    def _install(self, cid, chain, nxt, sigs, snapshots, new_keys, ckeys, witness_cls, frozen=()) -> int:
        self.registry.add_chain(cid, chain + [{"body": nxt, "sigs": sigs}])
        # The latest process of each key (current members win over retired ones).
        old = {w.pk: w for w in self.retired.get(cid, []) + self.all_witnesses(cid)}
        ws = []
        for kp in new_keys:
            w = witness_cls(kp, self.registry, self.clock)
            own = []  # a re-used key brings its own votes, even if it did not freeze (SPEC §5.4)
            if kp.pk in old and kp.pk not in frozen:
                own = [{s: [{"kind": "vote", "vote": v} for v in r.votes] for s, r in old[kp.pk].records.items()}]
            w.adopt(cid, nxt["version"], snapshots + own)
            ws.append(w)
        self.retired.setdefault(cid, []).extend(self.members.get(cid, []))
        self.retired_committees.setdefault(cid, []).extend(self.committees.get(cid, []))
        self.members[cid] = ws
        self.committees[cid] = self._stand_by(cid, nxt["version"], ckeys, snapshots)
        return nxt["version"]

    def find_votes(self, sigil: str) -> list:
        """Every vote any reachable witness has cast on ``sigil``."""
        out = []
        for cid in self.members:
            for w in self.witnesses(cid):
                out.extend(w.status(sigil)["votes"])
        return out
