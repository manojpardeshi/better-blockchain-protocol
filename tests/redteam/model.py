"""Witness-level schedule explorer: the search-based adversary for S1 and S2.

One constellation of ``n`` witnesses runs the *real* ``sigil.witness.Witness``
code for the honest members; ``b`` Byzantine members sign anything and join
any seal or death proof. A single adversarial owner signs every transition in
a pool of overlapping, conflicting transitions at random generations. Each
step either delivers a (possibly malformed) spend to an honest witness, asks
an honest witness to release the strongest death proof the adversary can
assemble, crashes/restarts an honest witness through its durable store, or
rotates the constellation at an adversarially chosen moment.

The search is randomised with light guidance: a step that leaves two tids
bound at one (sigil, gen) somewhere in the system is "interesting" and the
explorer biases toward releases and rotations from such states, because that
is where a double-spend would hide.

Invariants, checked after every step:

    S1  no sigil is consumed by two different complete transitions
    S2  no honest witness signed two tids for one (constellation, sigil, gen)

With ``b <= f`` both must always hold. With ``b > f`` they may break; the
runner can explore that regime to confirm the harness has teeth and to show
exactly where the math stops protecting (reported, not asserted).
"""

import os
import random
import tempfile

from sigil import KeyPair, Network, locks, model
from sigil.charter import faults, quorum
from sigil.store import WitnessStore
from sigil.witness import Rejected, Witness

from tests.adversary import Equivocator

FAR_FUTURE = 4_000_000_000


class Universe:
    def __init__(self, rng, *, n=4, byz=None, n_sigils=3, pool=6, max_gen=2,
                 use_store=False, allow_rotation=True):
        self.rng = rng
        self.n = n
        self.f = faults(n)
        self.q = quorum(n)
        self.byz_count = self.f if byz is None else byz
        self.use_store = use_store
        self.allow_rotation = allow_rotation
        self.net = Network()
        byz_map = {i: Equivocator for i in range(self.byz_count)}
        self._stores = {}
        self._open_stores = []  # every WitnessStore ever opened, closed in close()
        self.cid = self._make_constellation(n, byz_map)
        ws = self.net.all_witnesses(self.cid)
        self.byz = ws[: self.byz_count]
        self.honest = ws[self.byz_count:]
        self.owner = KeyPair.generate()
        self.parcels = {}
        for i in range(n_sigils):
            p = model.parcel(self.cid, "x", 1, locks.sig(self.owner.pk), f"salt{i}")
            self.parcels[model.sigil_of(p)] = p
        sigils = list(self.parcels)
        self.pool = []
        for k in range(pool):
            ins = rng.sample(sigils, rng.randint(1, min(3, len(sigils))))
            h = {"inputs": [[s, rng.randint(0, max_gen)] for s in ins], "body": f"{k:064x}"}
            self.pool.append((h, model.transition_id(h)))
        self.rotations = 0
        self.leaks = []  # malformed requests that raised something other than Rejected (BUG-3)

    def _make_constellation(self, n, byz_map):
        if not self.use_store:
            return self.net.create_constellation("model", n, byzantine=byz_map)
        # Store-backed honest witnesses so crash/restart can be exercised.
        keys = [KeyPair.generate() for _ in range(n)]
        from sigil.charter import charter_body, constellation_id
        body = charter_body("model", 0, [k.pk for k in keys], None)
        cid = constellation_id(body)
        self.net.registry.add_chain(cid, [{"body": body, "sigs": {}}])
        ws = []
        for i, kp in enumerate(keys):
            if i in byz_map:
                w = byz_map[i](kp, self.net.registry, self.net.clock)
            else:
                path = tempfile.mktemp(suffix=".db")
                self._stores[kp.pk] = path
                store = WitnessStore(path)
                self._open_stores.append(store)
                w = Witness(kp, self.net.registry, self.net.clock, store=store)
            w.join(cid, 0)
            ws.append(w)
        self.net.members[cid] = ws
        return cid

    # ----------------------------------------------------- adversary helpers

    def request(self, header, tid, sigil, *, malformed=False):
        p = self.parcels[sigil]
        u = locks.empty_unlock(FAR_FUTURE)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, tid, FAR_FUTURE)
        req = {"sigil": sigil, "header": header, "home": self.cid,
               "lock": p["lock"], "salt": p["salt"], "unlock": u}
        if malformed:
            spoil = self.rng.choice(["home", "unlock", "salt", "lock", "header", "sigil"])
            req[spoil] = self.rng.choice([None, {}, [], "xx", 42, {"op": "bogus"}])
        return req

    def honest_votes(self, sigil, gen):
        out = {}
        for w in self.honest:
            for v in w.status(sigil)["votes"]:
                if v["gen"] == gen:
                    out.setdefault(v["tid"], {})[v["witness"]] = v
        return out

    def complete(self, header, tid):
        for s, g in header["inputs"]:
            votes = dict(self.honest_votes(s, g).get(tid, {}))
            for w in self.byz:
                votes[w.pk] = w.forge(s, g, tid)
            if len(votes) < self.q:
                return False
        return True

    def death_proofs(self, header, tid):
        proofs = []
        for s, g in header["inputs"]:
            p = self.parcels[s]
            target = {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
            by_tid = self.honest_votes(s, g)
            for t, vs in by_tid.items():
                if t != tid:
                    votes = list(vs.values()) + [w.forge(s, g, t) for w in self.byz]
                    proofs.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target,
                                   "seal": model.seal_from_votes(votes)})
            others = {}
            for t, vs in by_tid.items():
                if t != tid:
                    others.update(vs)
            votes = list(others.values()) + [w.forge(s, g, "f" * 64) for w in self.byz]
            proofs.append({"kind": "votes", "sigil": s, "gen": g, "parcel": target, "votes": votes})
            # A deliberately invalid proof, to probe the release guard.
            proofs.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target,
                           "seal": model.seal_from_votes([w.forge(s, g, "e" * 64) for w in self.byz] or
                                                          [self.honest[0]._vote(s, g, "e" * 64)])})
        return proofs

    def _interesting(self):
        """Honest witnesses currently bound at a (sigil, gen) that has a sibling."""
        out = []
        for w in self.honest:
            for s, rec in w.records.items():
                if rec.tid is not None and rec.tid != "!contested":
                    out.append((w, s, rec))
        return out

    def close(self):
        """Close and delete any store-backed witness databases."""
        for store in self._open_stores:
            try:
                store.close()
            except Exception:
                pass
        self._open_stores = []
        for path in self._stores.values():
            try:
                os.unlink(path)
            except OSError:
                pass
        self._stores = {}

    def _restart(self, w):
        path = self._stores.get(w.pk)
        if path is None:
            return
        try:
            w.store.close()
        except Exception:
            pass
        store = WitnessStore(path)
        self._open_stores.append(store)
        fresh = Witness(w.kp, self.net.registry, self.net.clock, store=store)
        members = self.net.members[self.cid]
        members[members.index(w)] = fresh
        self.honest[self.honest.index(w)] = fresh

    def _rotate(self):
        try:
            keys = list(self.rng.sample([w.kp for w in self.honest], min(len(self.honest), self.n)))
            while len(keys) < self.n:
                keys.append(KeyPair.generate())
            self.rng.shuffle(keys)
            self.net.rotate(self.cid, keys)
            ws = self.net.all_witnesses(self.cid)
            self.honest = [w for w in ws if not isinstance(w, Equivocator)]
            self.byz = [w for w in ws if isinstance(w, Equivocator)]
            self.rotations += 1
        except RuntimeError:
            pass

    # ------------------------------------------------------------------ step

    def step(self):
        rng = self.rng
        bound = self._interesting()
        roll = rng.random()
        if roll < 0.55:
            header, tid = rng.choice(self.pool)
            s, _ = rng.choice(header["inputs"])
            malformed = rng.random() < 0.15
            try:
                rng.choice(self.honest).spend(self.request(header, tid, s, malformed=malformed))
            except Rejected:
                pass
            except Exception as e:
                # A malformed request should only ever be Rejected. In-process
                # spend leaks some exception types (BUG-3); the HTTP server masks
                # them as 400. Record, don't crash the search.
                self.leaks.append(f"{type(e).__name__}: {e}")
        elif roll < 0.85 and bound:
            # Guided: prefer releasing a binding that has a live sibling.
            w, s, rec = rng.choice(bound)
            proofs = self.death_proofs(rec.header, rec.tid)
            rng.shuffle(proofs)
            for proof in proofs:
                try:
                    w.release(s, proof)
                    break
                except Rejected:
                    continue
        elif roll < 0.93 and self.use_store and self.honest:
            self._restart(rng.choice(self.honest))
        elif roll < 1.0 and self.allow_rotation and self.rotations < 2:
            self._rotate()

    # ------------------------------------------------------------ invariants

    def check(self):
        self._check_s1()
        self._check_s2()

    def _check_s1(self):
        for s in self.parcels:
            done = {tid for h, tid in self.pool
                    if any(x == s for x, _ in h["inputs"]) and self.complete(h, tid)}
            if len(done) > 1:
                raise Violation("S1", f"sigil {s[:12]} consumed by {len(done)} complete transitions")

    def _check_s2(self):
        for w in self.honest:
            seen = {}
            for s, rec in w.records.items():
                for v in rec.votes:
                    key = (v["constellation"], v["sigil"], v["gen"])
                    if key in seen and seen[key] != v["tid"]:
                        raise Violation("S2", f"honest {w.pk[:8]} signed two tids at {key}")
                    seen[key] = v["tid"]


class Violation(Exception):
    def __init__(self, invariant, detail):
        super().__init__(f"{invariant}: {detail}")
        self.invariant = invariant


def explore(seeds, steps, *, n=4, byz=None, use_store=False, allow_rotation=True, start_seed=0):
    """Run the schedule explorer. Returns (violation_or_None, stats)."""
    stats = {"seeds": 0, "steps": 0, "completions": 0, "releases": 0, "rotations": 0, "leaks": 0}
    for seed in range(start_seed, start_seed + seeds):
        u = Universe(random.Random(seed), n=n, byz=byz, use_store=use_store,
                     allow_rotation=allow_rotation)
        try:
            for _ in range(steps):
                u.step()
                stats["steps"] += 1
                try:
                    u.check()
                except Violation as v:
                    return {"seed": seed, "invariant": v.invariant, "detail": str(v)}, stats
            stats["seeds"] += 1
            stats["rotations"] += u.rotations
            stats["leaks"] += len(u.leaks)
            stats["completions"] += sum(1 for h, t in u.pool if u.complete(h, t))
            stats["releases"] += sum(1 for w in u.honest for r in w.records.values()
                                     for e in r.log if e.get("kind") == "release")
        finally:
            u.close()
    return None, stats
