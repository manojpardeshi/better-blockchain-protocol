"""Randomised adversarial model checking of the core safety property.

    SAFETY: no sigil is consumed by two different *complete* transitions,
    where a transition is complete when every input is sealed to it at
    the generation its header names.

Setting: one constellation of 4 witnesses (quorum 3). Three run the real
honest ``Witness`` code; the fourth is Byzantine and will sign anything,
so the adversary may add its vote to any seal or death proof. The owner
of every sigil is also adversarial: it signs every transition in a pool
of overlapping, conflicting transitions with random generations. Each
step delivers a spend request to an honest witness, or asks an honest
witness to release a binding using the strongest death proof the
adversary can assemble from every vote cast so far.

The final test mutates the witness (accepting any death proof) and checks
that the explorer finds a double spend, so we know it has teeth.
"""

import os
import random
import unittest
from unittest import mock

from sigil import KeyPair, Network, locks, model
from sigil.charter import quorum
from sigil.witness import Rejected

SEEDS = int(os.environ.get("SIGIL_MODEL_SEEDS", "150"))
STEPS = int(os.environ.get("SIGIL_MODEL_STEPS", "120"))


class Universe:
    def __init__(self, rng: random.Random, n_sigils=3, pool=6, max_gen=2):
        self.rng = rng
        self.net = Network()
        self.cid = self.net.create_constellation("model", 4)
        ws = self.net.witnesses(self.cid)
        self.honest, self.byz = ws[:3], ws[3]
        self.q = quorum(4)
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

    def request(self, header, tid, sigil):
        p = self.parcels[sigil]
        u = locks.empty_unlock()
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, tid)
        return {"sigil": sigil, "header": header, "home": self.cid, "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def honest_votes(self, sigil, gen):
        out = {}
        for w in self.honest:
            for v in w.status(sigil)["votes"]:
                if v["gen"] == gen:
                    out.setdefault(v["tid"], {})[v["witness"]] = v
        return out  # tid -> {witness: vote}

    def sealed(self, sigil, gen, tid):
        return len(self.honest_votes(sigil, gen).get(tid, {})) + 1 >= self.q  # +1: the Byzantine vote

    def complete(self, header, tid):
        return all(self.sealed(s, g, tid) for s, g in header["inputs"])

    def death_proofs(self, header, tid):
        proofs = []
        for s, g in header["inputs"]:
            p = self.parcels[s]
            target = {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
            by_tid = self.honest_votes(s, g)
            for t, vs in by_tid.items():
                if t != tid:
                    votes = list(vs.values()) + [self.byz._vote(s, g, t)]
                    proofs.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target, "seal": model.seal_from_votes(votes)})
            others = {}
            for t, vs in by_tid.items():
                if t != tid:
                    others.update(vs)
            fake = "f" * 64
            votes = list(others.values()) + [self.byz._vote(s, g, fake)]
            proofs.append({"kind": "votes", "sigil": s, "gen": g, "parcel": target, "votes": votes})
        return proofs

    def step(self):
        rng = self.rng
        if rng.random() < 0.65:
            header, tid = rng.choice(self.pool)
            s, _ = rng.choice(header["inputs"])
            try:
                rng.choice(self.honest).spend(self.request(header, tid, s))
            except Rejected:
                pass
        else:
            w = rng.choice(self.honest)
            bound = [(s, r) for s, r in w.records.items() if r.tid is not None]
            if not bound:
                return
            s, rec = rng.choice(bound)
            proofs = self.death_proofs(rec.header, rec.tid)
            rng.shuffle(proofs)
            for proof in proofs:
                try:
                    w.release(s, proof)
                    break
                except Rejected:
                    continue

    def violation(self):
        for s in self.parcels:
            done = {tid for h, tid in self.pool if any(x == s for x, _ in h["inputs"]) and self.complete(h, tid)}
            if len(done) > 1:
                return s, done
        return None


def explore(seeds, steps):
    stats = {"releases": 0, "completions": 0}
    for seed in range(seeds):
        u = Universe(random.Random(seed))
        for _ in range(steps):
            u.step()
            bad = u.violation()
            if bad:
                return seed, bad, stats
        stats["releases"] += sum(1 for w in u.honest for r in w.records.values() for e in r.log if e["kind"] == "release")
        stats["completions"] += sum(1 for h, t in u.pool if u.complete(h, t))
    return None, None, stats


class ModelCheck(unittest.TestCase):
    def test_no_double_spend_under_adversarial_schedules(self):
        seed, bad, stats = explore(SEEDS, STEPS)
        self.assertIsNone(seed, f"double spend found with seed {seed}: {bad}")
        # Make sure the exploration actually exercised the interesting paths.
        self.assertGreater(stats["releases"], SEEDS // 2)
        self.assertGreater(stats["completions"], SEEDS // 2)

    def test_checker_detects_a_broken_witness(self):
        with mock.patch("sigil.witness.proves_dead", lambda *a: True):
            seed, bad, _ = explore(SEEDS, STEPS)
        self.assertIsNotNone(seed, "mutated witness should allow a double spend")


if __name__ == "__main__":
    unittest.main()
