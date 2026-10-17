"""An in-process network of constellations, for simulation and tests.

Witnesses are independent objects; the "network" is just the address book
plus fault injection (crashed witnesses). Nothing here is trusted by the
protocol: wallets verify every vote and seal they receive.
"""

from .charter import Registry, charter_body, charter_hash, constellation_id, quorum
from .crypto import KeyPair
from .stamps import StampMint
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
        self.down: set[str] = set()

    def create_constellation(self, name: str, n: int = 4, *, witness_cls=Witness,
                             byzantine: dict | None = None, stamps: bool = False,
                             stamp_bits: int = 1024) -> str:
        """Create a constellation of ``n`` witnesses.

        ``byzantine`` maps witness index -> Witness subclass to use instead.
        """
        keys = [KeyPair.generate() for _ in range(n)]
        body = charter_body(name, 0, [k.pk for k in keys], None)
        cid = constellation_id(body)
        self.registry.add_chain(cid, [{"body": body, "sigs": {}}])
        ws = []
        for i, kp in enumerate(keys):
            cls = (byzantine or {}).get(i, witness_cls)
            w = cls(kp, self.registry, self.clock, stamp_mint=StampMint(stamp_bits) if stamps else None)
            w.join(cid, 0)
            ws.append(w)
        self.members[cid] = ws
        return cid

    def witnesses(self, cid: str) -> list[Witness]:
        return [w for w in self.members.get(cid, []) if w.pk not in self.down]

    def all_witnesses(self, cid: str) -> list[Witness]:
        return list(self.members.get(cid, []))

    def rotate(self, cid: str, new_keys: list[KeyPair], witness_cls=Witness) -> int:
        """Replace a constellation's membership; returns the new version.

        Old members freeze and sign the new charter; new members adopt the
        union of the evidence handed over by the quorum that signed.
        """
        chain = self.registry.chain(cid)
        cur = chain[-1]["body"]
        nxt = charter_body(cur["name"], cur["version"] + 1, [k.pk for k in new_keys], charter_hash(cur))
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
        self.registry.add_chain(cid, chain + [{"body": nxt, "sigs": sigs}])
        ws = []
        for kp in new_keys:
            w = witness_cls(kp, self.registry, self.clock)
            w.adopt(cid, nxt["version"], snapshots)
            ws.append(w)
        self.members[cid] = ws
        return nxt["version"]

    def find_votes(self, sigil: str) -> list:
        """Every vote any reachable witness has cast on ``sigil``."""
        out = []
        for cid in self.members:
            for w in self.witnesses(cid):
                out.extend(w.status(sigil)["votes"])
        return out

