"""Gossip for charter chains and equivocation proofs.

Two kinds of public fact must reach every participant, and neither needs
ordering or consensus because each is self-verifying:

* **charter chains** (SPEC §3.7): when a constellation rotates, holders and
  other witnesses must learn the new version to count its votes;
* **equivocation proofs** (SPEC §3.8): when a witness signs two transitions
  for one ``(sigil, gen)``, every holder should stop counting its votes
  (``TrustPolicy.convict``) and anyone may claim its bond.

A by-product is **fork evidence**: two different charters for the same
version of a constellation, each signed by a quorum of the previous
version. Quorum intersection means at least one previous member signed
both, so a fork proves the constellation's old quorum is compromised.

Nothing gossiped is trusted. A ``GossipStore`` admits a chain only if
``Registry.add_chain`` verifies it (it extends what we know, no fork), a
proof only if ``verify_equivocation`` holds *and* the accused key is a
member of a charter we know, and fork evidence only if both branches
verify. Gossip is idempotent and order-independent apart from which branch
of a fork is seen first; see docs/WIRE.md "Gossip" for the threat notes.
"""

from .charter import Registry, verify_chain
from .crypto import verify
from .model import vote_payload
from .proofs import verify_equivocation, verify_vote
from .witness import Rejected

# Per-message caps (a POST /v0/gossip that exceeds them is refused whole).
MAX_PROOFS = 64          # equivocation proofs per message
MAX_FORKS = 16           # fork evidence items per message
MAX_CHARTERS = 64        # constellations per message
MAX_CHAIN = 1024         # charter versions per chain
# Per-store cap: new constellations accepted by gossip (extensions of known
# ones are always accepted). Genesis charters need no signatures, so
# without a cap anyone could fill a witness's registry for free. The same
# cap bounds the fork evidence a store keeps (one item per constellation,
# and anyone can fork a constellation whose keys they mint).
MAX_CONSTELLATIONS = 10_000

_MALFORMED = (KeyError, TypeError, ValueError, AttributeError, IndexError, RecursionError)


def _vote_copy(v: dict) -> dict:
    """Only the signed fields: extra fields in a gossiped vote are dropped."""
    out = vote_payload(v)
    out["sig"] = v["sig"]
    return out


def verify_fork(f: dict) -> bool:
    """Two different charters for one version, both quorum-signed by the shared prefix."""
    try:
        cid, prefix, a, b = f["constellation"], f["prefix"], f["a"], f["b"]
        return (isinstance(prefix, list) and len(prefix) >= 1 and len(prefix) < MAX_CHAIN
                and a["body"] != b["body"]
                and verify_chain(cid, prefix + [a]) and verify_chain(cid, prefix + [b]))
    except _MALFORMED:
        return False


def fork_signers(f: dict) -> set:
    """Members of the forked-from version who validly signed both branches."""
    members = set(f["prefix"][-1]["body"]["witnesses"])
    a, b = f["a"], f["b"]
    return {pk for pk in members
            if pk in a["sigs"] and pk in b["sigs"]
            and verify(pk, "charter", a["body"], a["sigs"][pk])
            and verify(pk, "charter", b["body"], b["sigs"][pk])}


def equivocations_in(votes: list) -> list:
    """Equivocation proofs hidden in a pile of votes (e.g. from STATUS or a death proof).

    Wallets see votes from many witnesses; any two valid votes by one key
    for different transitions at the same ``(constellation, sigil, gen)``
    are a proof. Invalid votes are skipped.
    """
    seen: dict[tuple, dict] = {}
    out, convicted = [], set()
    for v in votes:
        try:
            key = (v["witness"], v["constellation"], v["sigil"], v["gen"])
            other = seen.get(key)
            if v["witness"] in convicted or (other is not None and other["tid"] == v["tid"]):
                continue
            if not verify_vote(v):
                continue
            if other is None:
                seen[key] = v
            else:
                out.append({"a": other, "b": v})
                convicted.add(v["witness"])
        except _MALFORMED:
            continue
    return out


class GossipStore:
    """Verified charter chains, equivocation proofs and fork evidence.

    ``registry`` is shared with whoever uses it: a witness passes its own
    registry, a wallet passes ``network.registry`` (which is also its
    ``TrustPolicy.registry``), so whatever gossip verifies is immediately
    in force.
    """

    def __init__(self, registry: Registry | None = None, *, max_constellations: int = MAX_CONSTELLATIONS):
        self.registry = registry if registry is not None else Registry()
        self.max_constellations = max_constellations
        self.proofs: dict[str, dict] = {}   # witness pk -> first verified proof against it
        self.forks: dict[str, dict] = {}    # cid -> first verified fork evidence

    # ------------------------------------------------------------ charters

    def add_chain(self, cid: str, chain: list) -> bool:
        """Learn ``chain`` if it verifiably extends ours. Returns True if we learned something.

        A chain that diverges from ours is never adopted; if both branches
        verify, the divergence is kept as fork evidence instead.
        """
        try:
            if not isinstance(cid, str) or not isinstance(chain, list) or not 1 <= len(chain) <= MAX_CHAIN:
                return False
            known = self.registry.chain(cid)
            if not known and len(self.registry.ids()) >= self.max_constellations:
                return False
            for i in range(min(len(known), len(chain))):
                if chain[i]["body"] != known[i]["body"]:
                    self._note_fork(cid, known, chain, i)
                    return False
            if len(chain) <= len(known):
                return False
            # Same bodies as ours: keep our (already verified) prefix so a
            # different but valid signature subset is not mistaken for a fork.
            self.registry.add_chain(cid, known + chain[len(known):])
            return True
        except _MALFORMED:
            return False

    def _note_fork(self, cid: str, known: list, chain: list, i: int) -> None:
        if cid in self.forks or i == 0:  # i == 0: a different genesis is a different cid, not a fork
            return
        if len(self.forks) >= self.max_constellations:
            return
        f = {"constellation": cid, "prefix": known[:i], "a": known[i], "b": chain[i]}
        if verify_chain(cid, chain[: i + 1]):  # our branch is already verified
            self.forks[cid] = f

    def add_fork(self, f: dict) -> bool:
        try:
            cid = f["constellation"]
            if not isinstance(cid, str) or cid in self.forks or len(self.forks) >= self.max_constellations:
                return False
            if not verify_fork(f):
                return False
            self.forks[cid] = {k: f[k] for k in ("constellation", "prefix", "a", "b")}
            return True
        except _MALFORMED:
            return False

    # -------------------------------------------------------------- proofs

    def add_proof(self, proof: dict) -> bool:
        """Keep a verified proof against a witness of a charter we know (one per witness)."""
        try:
            if not verify_equivocation(proof):
                return False
            a, b = proof["a"], proof["b"]
            pk = a["witness"]
            if pk in self.proofs:
                return False
            # Only members of a known charter: proofs against throwaway keys
            # convict nobody and would let anyone grow our store for free.
            charter = self.registry.charter(a["constellation"], a["version"])
            if charter is None or pk not in charter["witnesses"]:
                return False
            self.proofs[pk] = {"a": _vote_copy(a), "b": _vote_copy(b)}
            return True
        except _MALFORMED:
            return False

    def convicted(self) -> set:
        return set(self.proofs)

    # ------------------------------------------------------------- messages

    def merge(self, msg: dict) -> dict:
        """Admit everything verifiable in a gossip message; return what was accepted.

        Charters first, so proofs against newly learned members are admitted
        in the same pass. Structurally bad messages raise ``ValueError``;
        individually invalid items are just dropped.
        """
        charters, proofs, forks = check_message(msg)
        out = {"charters": 0, "proofs": 0, "forks": 0}
        for cid, chain in charters.items():
            out["charters"] += self.add_chain(cid, chain)
        for f in forks:
            out["forks"] += self.add_fork(f)
        for p in proofs:
            out["proofs"] += self.add_proof(p)
        return out

    def snapshot(self) -> dict:
        """Everything we know, as a gossip message (uncapped: callers batch it)."""
        return {"charters": {cid: self.registry.chain(cid) for cid in self.registry.ids()},
                "proofs": list(self.proofs.values()), "forks": list(self.forks.values())}

    def apply(self, policy) -> int:
        """Convict every witness we hold a proof against; returns how many were new."""
        new = 0
        for pk, p in self.proofs.items():
            if pk not in policy.convicted and policy.convict(p):
                new += 1
        return new


def check_message(msg) -> tuple[dict, list, list]:
    """Shape and size checks for a gossip message (raises ``ValueError``)."""
    if not isinstance(msg, dict):
        raise ValueError("gossip message must be an object")
    charters = msg.get("charters", {})
    proofs = msg.get("proofs", [])
    forks = msg.get("forks", [])
    if not isinstance(charters, dict) or not isinstance(proofs, list) or not isinstance(forks, list):
        raise ValueError("charters must be an object, proofs and forks lists")
    if len(charters) > MAX_CHARTERS:
        raise ValueError(f"at most {MAX_CHARTERS} charter chains per message")
    if any(not isinstance(c, list) or len(c) > MAX_CHAIN for c in charters.values()):
        raise ValueError(f"charter chains must be lists of at most {MAX_CHAIN}")
    if len(proofs) > MAX_PROOFS:
        raise ValueError(f"at most {MAX_PROOFS} proofs per message")
    if len(forks) > MAX_FORKS:
        raise ValueError(f"at most {MAX_FORKS} forks per message")
    return charters, proofs, forks


def batches(msg: dict) -> list:
    """Split a gossip message into messages within the per-message caps."""
    charters = list(msg.get("charters", {}).items())
    proofs, forks = list(msg.get("proofs", [])), list(msg.get("forks", []))
    out = []
    while charters or proofs or forks:
        out.append({"charters": dict(charters[:MAX_CHARTERS]), "proofs": proofs[:MAX_PROOFS],
                    "forks": forks[:MAX_FORKS]})
        charters, proofs, forks = charters[MAX_CHARTERS:], proofs[MAX_PROOFS:], forks[MAX_FORKS:]
    return out


# ------------------------------------------------------------------ rounds

def _peers(network) -> list:
    """Every reachable witness client of a ``RemoteNetwork`` (or a plain list of peers)."""
    if isinstance(network, list):
        return network
    out, seen = [], set()
    for cid in list(network.urls):
        for w in network.all_witnesses(cid):
            if w.url not in seen:
                seen.add(w.url)
                out.append(w)
    return out


def gossip_round(network, store: GossipStore) -> dict:
    """One anti-entropy round: pull from every reachable peer, then push what each lacks.

    ``network`` is a ``RemoteNetwork`` (all its witnesses) or a list of
    peers with ``pull()`` and ``gossip(msg)`` (``RemoteWitness`` has both).
    Unreachable or misbehaving peers are skipped. Returns counts of what
    ``store`` learned and how many items were pushed.
    """
    from .server import Unreachable  # avoid an import cycle (server imports gossip)

    views = []
    for peer in _peers(network):
        try:
            theirs = peer.pull()
        except Rejected:  # includes Unreachable
            continue
        if isinstance(theirs, dict):
            views.append((peer, _parts(theirs)))
    # Admit charters from every peer before any proof, so a proof against a
    # member of a rotation we only just learned is not dropped. A peer may
    # legitimately hold more than one message's worth, so items are admitted
    # one by one rather than through ``merge``'s per-message caps.
    learned = {"charters": 0, "proofs": 0, "forks": 0}
    for _, (charters, _, _) in views:
        for cid, chain in charters.items():
            learned["charters"] += store.add_chain(cid, chain)
    for _, (_, _, forks) in views:
        for f in forks:
            learned["forks"] += store.add_fork(f)
    for _, (_, proofs, _) in views:
        for p in proofs:
            learned["proofs"] += store.add_proof(p)
    pushed = 0
    for peer, (charters, proofs, forks) in views:
        have = {cid: len(c) for cid, c in charters.items() if isinstance(c, list)}
        accused = {_get(p, "a", "witness") for p in proofs}
        forked = {_get(f, "constellation") for f in forks}
        msg = {
            "charters": {cid: store.registry.chain(cid) for cid in store.registry.ids()
                         if len(store.registry.chain(cid)) > have.get(cid, 0)},
            "proofs": [p for pk, p in store.proofs.items() if pk not in accused],
            "forks": [f for cid, f in store.forks.items() if cid not in forked],
        }
        for m in batches(msg):
            try:
                peer.gossip(m)
                pushed += len(m["charters"]) + len(m["proofs"]) + len(m["forks"])
            except Unreachable:
                break
            except Rejected:  # a peer refusing one batch must not stop the round
                continue
    return {"learned": learned, "pushed": pushed, "peers": len(views)}


def _parts(msg: dict) -> tuple[dict, list, list]:
    """The three item collections of a pulled snapshot, empty where malformed."""
    charters, proofs, forks = msg.get("charters"), msg.get("proofs"), msg.get("forks")
    return (charters if isinstance(charters, dict) else {},
            proofs if isinstance(proofs, list) else [],
            forks if isinstance(forks, list) else [])


def _get(obj, *path):
    for k in path:
        if not isinstance(obj, dict):
            return None
        obj = obj.get(k)
    return obj if isinstance(obj, str) else None
