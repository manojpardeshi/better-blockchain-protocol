"""What the chaos harness observes, and the global safety invariants it checks.

``Observer`` sees every request and reply that passes through a ``FaultProxy`` (and the
final STATUS sweep), and keeps every *verified* vote in them, every SPEND header (so a tid
can be resolved to the inputs it consumes), and which process emitted which vote.

``check`` evaluates, after a run (docs/SPEC.md §4, §5, §8):

* **S1 no double consumption**: no sigil is an input of two complete transitions, where a
  transition is complete when every input has a valid seal, built from *any* votes seen
  anywhere (witness replies, STATUS, dossiers) and checked against the final charter chains.
  **S1b**: no two tids are sealed at one (sigil, gen), in any versions (Lemma 1 + rotation).
* **S2 no honest equivocation**: no honest witness key signed two tids for one
  (constellation, sigil, gen), across processes and versions.
* **S5 durability**: every vote an honest process sent is still in its STATUS at the end
  (after any number of SIGKILLs and restarts, disk-full episodes included).
* **S6 expiry**: no honest, correctly clocked witness ever voted for a transition at a
  generation whose pledge an honest wallet had released (SPEC §4 rule 3, §5.1 step 4).
* **S3 conservation** and **S4 fresh verification** are wallet-level and live in run.py.
"""

import threading
from collections import defaultdict

from sigil.charter import quorum
from sigil.model import VOTE_FIELDS, transition_id
from sigil.proofs import verify_seal, verify_vote

VOTE_KEYS = frozenset(VOTE_FIELDS) | {"sig"}


def _vote_key(v: dict) -> tuple:
    return (v["witness"], v["constellation"], v["version"], v["sigil"], v["gen"], v["tid"])


class Observer:
    def __init__(self):
        self.lock = threading.Lock()
        self.votes: dict[tuple, dict] = {}          # vote key -> vote (verified)
        self.headers: dict[str, dict] = {}          # tid -> header (from SPEND / MIRROR requests)
        self.emitted: dict[str, set] = defaultdict(set)   # proxy name -> vote keys it relayed from its process
        self.pk_of: dict[str, str] = {}             # proxy name -> pk of the process behind it
        self.methods: dict[str, int] = defaultdict(int)
        self.replies: dict[str, int] = defaultdict(int)
        self._checked: dict[str, bool] = {}         # sig -> verified?
        self.notes: list = []

    # ------------------------------------------------------------ collection

    def _verified(self, v: dict) -> bool:
        sig = v.get("sig")
        if not isinstance(sig, str):
            return False
        ok = self._checked.get(sig)
        if ok is None:
            ok = self._checked[sig] = verify_vote(v)
        return ok

    def _scan(self, x, out: list, depth: int = 0) -> None:
        if depth > 12:
            return
        if isinstance(x, dict):
            if VOTE_KEYS <= x.keys():
                out.append(x)
            for y in x.values():
                self._scan(y, out, depth + 1)
        elif isinstance(x, list):
            for y in x:
                self._scan(y, out, depth + 1)

    def add_vote(self, v: dict, source: str | None = None) -> bool:
        try:
            if not self._verified(v):
                return False
            k = _vote_key(v)
        except (TypeError, KeyError, ValueError):
            return False
        with self.lock:
            self.votes.setdefault(k, {f: v[f] for f in VOTE_KEYS})
            if source is not None and self.pk_of.get(source) == v["witness"]:
                self.emitted[source].add(k)
        return True

    def add_header(self, header) -> None:
        try:
            tid = transition_id(header)
        except (TypeError, KeyError, ValueError, AttributeError):
            return
        with self.lock:
            self.headers.setdefault(tid, header)

    def record(self, source: str, method: str, req, status, rep) -> None:
        with self.lock:
            self.methods[method] += 1
            self.replies[f"{method}:{status}"] += 1
        if isinstance(req, dict):
            r = req.get("request")
            if isinstance(r, dict) and "header" in r:
                self.add_header(r["header"])
            found: list = []
            self._scan(req, found)
            for v in found:
                self.add_vote(v)
        if rep is not None:
            found = []
            self._scan(rep, found)
            for v in found:
                self.add_vote(v, source)

    # ------------------------------------------------------------ analysis

    def seals(self, registry, extra_seals=()) -> dict:
        """``{(sigil, gen): {tid: [(cid, version)]}}`` of every valid seal assemblable."""
        groups: dict[tuple, set] = defaultdict(set)
        with self.lock:
            votes = list(self.votes.values())
        for v in votes:
            groups[(v["constellation"], v["version"], v["sigil"], v["gen"], v["tid"])].add(v["witness"])
        out: dict[tuple, dict] = defaultdict(lambda: defaultdict(list))
        for (cid, version, s, g, t), pks in groups.items():
            charter = registry.charter(cid, version)
            if charter is None:
                continue
            if len(pks & set(charter["witnesses"])) >= quorum(len(charter["witnesses"])):
                out[(s, g)][t].append((cid, version))
        for seal in extra_seals:
            if verify_seal(seal, registry):
                out[(seal["sigil"], seal["gen"])][seal["tid"]].append((seal["constellation"], seal["version"]))
        return out


def check(obs: Observer, registry, *, honest: set, clocked: set, released: list, final_status: dict,
          extra_seals=(), extra_headers=None) -> list:
    """Every safety violation found, as ``{"kind", ...}`` dicts.

    ``honest``: witness keys that run honest code; ``clocked``: those whose clock stayed
    within the configured skew bound (S6 applies to them only); ``released``: pledges
    ``(sigil, gen, tid)`` honest wallets released; ``final_status``: ``{proxy name:
    {sigil: status}}`` read from every honest process at the end.
    """
    violations = []
    headers = dict(obs.headers)
    headers.update(extra_headers or {})
    sealed = obs.seals(registry, extra_seals)

    # S1b: one sealed tid per (sigil, gen)
    for (s, g), tids in sealed.items():
        if len(tids) > 1:
            violations.append({"kind": "S1b-two-seals-one-generation", "sigil": s, "gen": g,
                               "tids": {t: v for t, v in tids.items()}})
    # S1: no sigil consumed by two complete transitions
    sealed_set = {(s, g, t) for (s, g), tids in sealed.items() for t in tids}
    complete = [t for t, h in headers.items()
                if h.get("inputs") and all((s, g, t) in sealed_set for s, g in h["inputs"])]
    consumers: dict[str, set] = defaultdict(set)
    for t in complete:
        for s, _g in headers[t]["inputs"]:
            consumers[s].add(t)
    for s, ts in consumers.items():
        if len(ts) > 1:
            violations.append({"kind": "S1-double-consumption", "sigil": s, "tids": sorted(ts)})

    # S2: an honest key never signs two tids for one (constellation, sigil, gen)
    with obs.lock:
        votes = list(obs.votes.values())
    by: dict[tuple, set] = defaultdict(set)
    for v in votes:
        if v["witness"] in honest:
            by[(v["witness"], v["constellation"], v["sigil"], v["gen"])].add(v["tid"])
    for (pk, cid, s, g), ts in by.items():
        if len(ts) > 1:
            violations.append({"kind": "S2-honest-equivocation", "witness": pk, "sigil": s, "gen": g,
                               "tids": sorted(ts)})

    # S5: every vote an honest process sent is still in its STATUS at the end
    for source, keys in obs.emitted.items():
        pk = obs.pk_of.get(source)
        if pk not in honest or source not in final_status:
            continue
        held = set()
        for st in final_status[source].values():
            for v in (st or {}).get("votes", []):
                try:
                    held.add(_vote_key(v))
                except (KeyError, TypeError):
                    pass
        for k in keys:
            if k not in held:
                violations.append({"kind": "S5-vote-forgotten", "process": source, "vote": list(k)})

    # S6: nothing voted (honest, well-clocked) for a released pledge
    rel = set(released)
    for v in votes:
        if v["witness"] in honest and v["witness"] in clocked and (v["sigil"], v["gen"], v["tid"]) in rel:
            violations.append({"kind": "S6-vote-after-pledge-release", "witness": v["witness"],
                               "sigil": v["sigil"], "gen": v["gen"], "tid": v["tid"], "time": v["time"]})
    return violations
