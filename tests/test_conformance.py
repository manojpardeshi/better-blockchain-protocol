"""Code-to-model conformance: the real ``Witness`` refines the abstract
model that ``formal/SigilProofs.tla`` proves safe, and a regression repro
for a double-spend the TLAPS proof's no-rotation scope does not cover.

WHAT THIS CHECKS
----------------
``formal/SigilProofs.tla`` is an abstract transition system over honest and
Byzantine witnesses whose safety theorem (SPEC Section 8) is machine-checked
by TLAPS for arbitrary sizes. This test closes the gap between that abstract
model and the executable ``sigil.witness.Witness`` by running the REAL witness
code under randomised adversarial schedules and asserting, after every step,
that the witness's state and the votes it emits are allowed by the abstract
model's transition relation and satisfy its invariants.

REFINEMENT MAPPING (abstract  <-  concrete)
-------------------------------------------
    gen[w][s]    <-  w.records[s].gen            (0 when absent)
    bound[w][s]  <-  w.records[s].tid            (NoTid <- None)
    votes        <-  the multiset of (constellation, witness, sigil, gen, tid)
                     over every w.records[s].votes of every honest witness

The abstract actions (SigilProofs.tla) and the invariants we mirror:

* ``Spend(w,s,t)`` precondition (SPEC 5.1 step 4): an honest witness emits a
  vote for (s,g,t) only when, just before, either g = gen[w][s] and
  bound[w][s] in {NoTid, t} (bind / re-vote), or g > gen[w][s] and
  bound[w][s] = NoTid (generation jump while unbound). After it, gen[w][s] = g
  and bound[w][s] = t and the vote carries (cid, pk, s, g, t).
* ``HonestNoEquiv``: no honest witness holds two votes with the same
  (constellation, sigil, gen) and different tids.
* ``VoteBelowGen``: every vote an honest witness cast is at a generation
  <= its current gen for that sigil.
* ``BoundVote``: bound to t (not contested) iff there is a vote at the current
  gen for t (modulo the rotation-only ``abstain`` flag).
* generation monotonicity: gen[w][s] never decreases.
* ``Safety`` / ``OneSealPerGen`` (SPEC Section 8): over all votes in the
  network, no (sigil, gen) is sealed to two tids within one charter version,
  and no sigil is consumed by two different complete transitions.

The default run is fast (< 30 s). Scale with SIGIL_CONFORMANCE_SEEDS and
SIGIL_CONFORMANCE_STEPS.
"""

import os
import random
import unittest

from sigil import KeyPair, Network, locks, model
from sigil.charter import quorum
from sigil.proofs import verify_seal, verify_vote
from sigil.witness import CONTESTED, Conflict, Rejected

SEEDS = int(os.environ.get("SIGIL_CONFORMANCE_SEEDS", "40"))
STEPS = int(os.environ.get("SIGIL_CONFORMANCE_STEPS", "60"))


class ModelViolation(AssertionError):
    """The concrete witness left a state the abstract model forbids."""


def as_vote_tuple(v: dict) -> tuple:
    return (v["constellation"], v["witness"], v["sigil"], v["gen"], v["tid"])


class Mirror:
    """The abstract model's checks, applied to the real witnesses.

    Holds the previous ``(gen, tid)`` per (witness, sigil) so it can verify
    each concrete step was an abstract-legal transition, not just that the
    resulting state is well-formed.
    """

    def __init__(self, honest):
        self.honest = honest
        self.snap = {}  # (pk, sigil) -> (gen, tid)

    def rec(self, w, s):
        r = w.records.get(s)
        return (0, None) if r is None else (r.gen, r.tid)

    # ---- per-witness invariants (abstract VotesShape / NoEquiv / etc.) ----

    def check_witness(self, w):
        for s, r in w.records.items():
            # VoteBelowGen and HonestNoEquiv over this witness's own votes.
            seen = {}
            for v in r.votes:
                if not verify_vote(v):
                    raise ModelViolation(f"{w.pk[:8]} emitted an unverifiable vote on {s[:8]}")
                if v["witness"] != w.pk or v["constellation"] != w.cid:
                    raise ModelViolation(f"{w.pk[:8]} vote carries a foreign identity")
                if not (isinstance(v["gen"], int) and 0 <= v["gen"] <= r.gen):
                    raise ModelViolation(f"VoteBelowGen: {w.pk[:8]} voted at gen {v['gen']} > {r.gen}")
                key = v["gen"]
                if key in seen and seen[key] != v["tid"]:
                    raise ModelViolation(
                        f"HonestNoEquiv: {w.pk[:8]} has two tids at (s,{key}) on {s[:8]}")
                seen[key] = v["tid"]
            # BoundVote (no rotation => abstain is never set, so this is exact):
            # bound to t at the current gen  <=>  a vote for t at that gen.
            if not r.abstain and r.tid not in (None, CONTESTED):
                if seen.get(r.gen) != r.tid:
                    raise ModelViolation(f"BoundVote: {w.pk[:8]} bound to {r.tid[:6]} but no vote at gen {r.gen}")
            if not r.abstain and r.tid is None and r.gen in seen:
                raise ModelViolation(f"BoundVote: {w.pk[:8]} unbound yet voted at current gen {r.gen}")

    # ---- transition legality (abstract Spend precondition) ----

    def snapshot(self):
        self.snap = {(w.pk, s): self.rec(w, s) for w in self.honest for s in w.records}

    def check_spend(self, w, s, before, vote):
        """A spend that returned ``vote`` must match an abstract Spend step."""
        g, t = vote["gen"], vote["tid"]
        g0, t0 = before
        legal = (g == g0 and t0 in (None, t)) or (g > g0 and t0 is None)
        if not legal:
            raise ModelViolation(
                f"Spend precondition: {w.pk[:8]} voted (s,{g},{t[:6]}) from record (gen={g0}, tid={t0})")
        after_g, after_t = self.rec(w, s)
        if after_g != g or after_t != t:
            raise ModelViolation(f"Spend postcondition: record ({after_g},{after_t}) != vote ({g},{t[:6]})")

    def check_monotone(self):
        for w in self.honest:
            for s in w.records:
                g0 = self.snap.get((w.pk, s), (0, None))[0]
                if self.rec(w, s)[0] < g0:
                    raise ModelViolation(f"gen went backwards for {w.pk[:8]} on {s[:8]}")


class Universe:
    """One constellation of 4 real witnesses (3 honest + 1 Byzantine),
    an equivocating owner, and a scheduler that delivers well-formed and
    malformed spends, releases with assembled death proofs, and status
    queries -- the same adversary shape as tests/test_model_check.py, but
    every honest step is checked against the abstract model."""

    def __init__(self, rng, n_sigils=3, pool=6, max_gen=2):
        self.rng = rng
        self.net = Network()
        self.cid = self.net.create_constellation("conf", 4)
        ws = self.net.witnesses(self.cid)
        self.honest, self.byz = ws[:3], ws[3]
        self.q = quorum(4)
        self.owner = KeyPair.generate()
        self.exp = int(self.net.clock()) + 10 ** 9  # far future: never expired here
        self.mirror = Mirror(self.honest)
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

    def request(self, header, tid, sigil, *, expires=None):
        p = self.parcels[sigil]
        exp = self.exp if expires is None else expires
        u = locks.empty_unlock(exp)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, tid, exp)
        return {"sigil": sigil, "header": header, "home": self.cid,
                "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def honest_votes(self, sigil, gen):
        out = {}
        for w in self.honest:
            for v in w.status(sigil)["votes"]:
                if v["gen"] == gen:
                    out.setdefault(v["tid"], {})[v["witness"]] = v
        return out

    def sealed(self, sigil, gen, tid):
        return len(self.honest_votes(sigil, gen).get(tid, {})) + 1 >= self.q  # +1 Byzantine

    def complete(self, header, tid):
        return all(self.sealed(s, g, tid) for s, g in header["inputs"])

    def death_proofs(self, header, tid):
        proofs = []
        for s, g in header["inputs"]:
            p = self.parcels[s]
            target = {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
            by_tid = self.honest_votes(s, g)
            others = {}
            for t, vs in by_tid.items():
                if t != tid:
                    votes = list(vs.values()) + [self.byz._vote(s, g, t)]
                    proofs.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target,
                                   "seal": model.seal_from_votes(votes)})
                    others.update(vs)
            votes = list(others.values()) + [self.byz._vote(s, g, "f" * 64)]
            proofs.append({"kind": "votes", "sigil": s, "gen": g, "parcel": target, "votes": votes})
        return proofs

    def step(self):
        rng = self.rng
        self.mirror.snapshot()
        roll = rng.random()
        if roll < 0.55:  # well-formed spend
            header, tid = rng.choice(self.pool)
            s, _ = rng.choice(header["inputs"])
            w = rng.choice(self.honest)
            before = self.mirror.rec(w, s)
            try:
                v = w.spend(self.request(header, tid, s))
            except (Rejected, Conflict):
                v = None
            if v is not None:
                self.mirror.check_spend(w, s, before, v)
        elif roll < 0.75:  # release with the strongest assembled proof
            w = rng.choice(self.honest)
            bound = [(s, r) for s, r in w.records.items() if r.tid not in (None, CONTESTED)]
            if bound:
                s, rec = rng.choice(bound)
                proofs = self.death_proofs(rec.header, rec.tid)
                rng.shuffle(proofs)
                for proof in proofs:
                    try:
                        w.release(s, proof)
                        break
                    except Rejected:
                        continue
        elif roll < 0.9:  # malformed request: must be refused cleanly, state untouched
            w = rng.choice(self.honest)
            s = rng.choice(list(self.parcels))
            before = self.mirror.rec(w, s)
            bad = self.rng.choice([
                {"sigil": s, "home": self.cid},                      # missing fields
                {"sigil": s, "home": "elsewhere", "header": {}, "lock": {}, "salt": "", "unlock": {}},
                self._expired_request(s),                            # expired authorisation
                "not a dict",
            ])
            try:
                w.spend(bad)
            except (Rejected, Conflict):
                pass
            except Exception as e:  # noqa: BLE001 - any other escape is a conformance failure
                raise ModelViolation(f"spend leaked {type(e).__name__} on malformed input: {e!r}")
            if self.mirror.rec(w, s) != before:
                raise ModelViolation("a refused spend mutated the record")
        else:  # status query must never mutate state
            w = rng.choice(self.honest)
            s = rng.choice(list(self.parcels))
            before = self.mirror.rec(w, s)
            w.status(s)
            if self.mirror.rec(w, s) != before:
                raise ModelViolation("status mutated the record")
        # Invariants after every step.
        self.mirror.check_monotone()
        for w in self.honest:
            self.mirror.check_witness(w)

    def _expired_request(self, s):
        header, tid = self.rng.choice(self.pool)
        if not any(x == s for x, _ in header["inputs"]):
            header = {"inputs": [[s, 0]], "body": "e" * 64}
            tid = model.transition_id(header)
        return self.request(header, tid, s, expires=int(self.net.clock()) - 1)

    def global_safety(self):
        """SPEC Section 8 over the real network's votes (one charter version)."""
        for s in self.parcels:
            # Lemma 1: at most one tid sealed per (s, gen).
            for g in range(5):
                sealed_tids = {t for h, tid in self.pool for (x, gg) in h["inputs"]
                               if x == s and gg == g for t in [tid] if self.sealed(s, g, t)}
                if len(sealed_tids) > 1:
                    return f"two seals at ({s[:8]},{g}): {sealed_tids}"
            # Theorem: no two complete transitions consume s.
            done = {tid for h, tid in self.pool
                    if any(x == s for x, _ in h["inputs"]) and self.complete(h, tid)}
            if len(done) > 1:
                return f"double consumption of {s[:8]}: {done}"
        return None


class ConformanceTests(unittest.TestCase):
    def _run(self, seeds, steps):
        for seed in range(seeds):
            u = Universe(random.Random(seed))
            for _ in range(steps):
                u.step()
            bad = u.global_safety()
            self.assertIsNone(bad, f"seed {seed}: {bad}")

    def test_witness_refines_abstract_model(self):
        """The real Witness never leaves the abstract model's reachable set
        and never violates SPEC Section 8 (single charter version, no rotation)."""
        self._run(SEEDS, STEPS)

    def test_detects_a_broken_witness(self):
        """A witness that forgets its generation floor (votes at stale gens)
        must be caught by the mirror -- so we know the checks have teeth."""
        from unittest import mock
        from sigil.witness import Record, Witness

        real = Witness.spend

        def amnesiac(self, req):
            # Drop the stale-generation guard: reset the record so any gen binds.
            s = req.get("sigil") if isinstance(req, dict) else None
            if s in self.records:
                self.records[s] = Record()
            return real(self, req)

        found = False
        with mock.patch.object(Witness, "spend", amnesiac):
            for seed in range(SEEDS):
                u = Universe(random.Random(seed))
                try:
                    for _ in range(STEPS):
                        u.step()
                    if u.global_safety():
                        found = True
                        break
                except ModelViolation:
                    found = True
                    break
        self.assertTrue(found, "the mirror failed to catch an amnesiac witness")


class RotationRegressionTests(unittest.TestCase):
    """Regressions for two rotation bugs the bounded explorer found.

    The TLAPS proof (formal/SigilProofs.tla) models one charter version.
    Rotation (SPEC 5.4) is model-checked in formal/SigilRot.tla, whose
    "sibling" mode is the ADOPT implemented in sigil/witness.py.
    """

    def _scenario(self, sealed: str):
        """The owner equivocates on s at generation 0 with Tb = {(s,0),(x,0)}
        and Ta = {(s,0)}. ``sealed`` names the one a quorum seals; one witness
        binds the other. x is consumed by Ty, so Tb is provably dead, and the
        witnesses bound to Tb release s. Then the constellation rotates.

        Both orders leave ADOPT the same evidence, binds {(0,Tb), (0,Ta)} with
        Tb dead, but need opposite outcomes, so ADOPT must not inherit Ta.
        """
        net = Network()
        X = net.create_constellation("orion", 4)
        owner = KeyPair.generate()
        exp = int(net.clock()) + 10 ** 9

        def mk(salt):
            p = model.parcel(X, "x", 1, locks.sig(owner.pk), salt)
            return p, model.sigil_of(p)

        ps, s = mk("s")
        px, x = mk("x")
        tgt = lambda p: {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
        hdr = lambda inputs, tag: {"inputs": [list(i) for i in inputs], "body": tag * 64}

        def req(h, sigil, p):
            u = locks.empty_unlock(exp)
            u["sigs"][owner.pk] = locks.sign_unlock(owner, sigil, model.transition_id(h), exp)
            return {"sigil": sigil, "header": h, "home": X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

        Ty, Tb, Ta, Tg = hdr([(x, 0)], "1"), hdr([(s, 0), (x, 0)], "2"), hdr([(s, 0)], "3"), hdr([(s, 1)], "4")
        k = net.witnesses(X)
        seal_y = model.seal_from_votes([w.spend(req(Ty, x, px)) for w in k])
        quorum_tx, single_tx = (Tb, Ta) if sealed == "Tb" else (Ta, Tb)
        seal_q = model.seal_from_votes([w.spend(req(quorum_tx, s, ps)) for w in k[:3]])
        k[3].spend(req(single_tx, s, ps))
        dp_b = {"kind": "seal", "sigil": x, "gen": 0, "parcel": tgt(px), "seal": seal_y}
        for w in (k[:3] if sealed == "Tb" else k[3:]):
            w.release(s, dp_b)
        net.rotate(X, [KeyPair.generate() for _ in range(4)])

        def try_seal(h):
            votes = []
            for w in net.witnesses(X):
                try:
                    votes.append(w.spend(req(h, s, ps)))
                except (Rejected, Conflict):
                    pass
            seal = model.seal_from_votes(votes) if votes else None
            return seal if seal and verify_seal(seal, net.registry) else None

        def release_all(proof):
            for w in net.witnesses(X):
                try:
                    w.release(s, proof)
                except Rejected:
                    pass

        return net, X, s, ps, tgt, (Ta, Tg), seal_q, try_seal, release_all

    def test_adopt_does_not_reopen_a_consumed_generation(self):
        """Tb sealed then released: the new charter must never seal Ta at (s,0).

        The old ADOPT inherited the lone live binding Ta, so the new witnesses
        sealed Ta at (s,0). Tb's old seal then proved Ta dead, s moved to
        generation 1 and Tg was sealed too: s was consumed twice.
        """
        net, X, s, ps, tgt, (Ta, Tg), seal_b, try_seal, release_all = self._scenario("Tb")
        for w in net.witnesses(X):
            self.assertEqual(w.records[s].tid, CONTESTED)
        self.assertIsNone(try_seal(Ta), "the new charter sealed a second tid at (s,0)")
        # The owner recovers: Tb's seal proves Ta dead, so s moves on to generation 1.
        release_all({"kind": "seal", "sigil": s, "gen": 0, "parcel": tgt(ps), "seal": seal_b})
        self.assertIsNotNone(try_seal(Tg))
        self.assertIsNone(try_seal(Ta))

    def test_adopt_keeps_a_sealed_sibling(self):
        """Dual case: Ta sealed, Tb released. s is consumed by Ta, so Tg must never be sealed."""
        net, X, s, ps, tgt, (Ta, Tg), seal_a, try_seal, release_all = self._scenario("Ta")
        self.assertIsNone(try_seal(Tg))
        # Nothing proves Ta dead: the only other seal at (s,0) does not exist.
        release_all({"kind": "seal", "sigil": s, "gen": 0, "parcel": tgt(ps), "seal": seal_a})
        self.assertIsNone(try_seal(Tg), "s was consumed by Ta and again by Tg")
        self.assertTrue(verify_seal(seal_a, net.registry))

    def test_freeze_commits_to_a_single_successor_charter(self):
        """Regression (sigil/witness.py Witness.freeze): a frozen witness signed
        MORE THAN ONE successor charter, so honest witnesses can be made to
        certify two conflicting version-(v+1) charters, each reaching a v0
        quorum -- a charter fork.

        Both forks then pass charter.verify_chain, and a victim that adopts
        the attacker's fork trusts attacker keys as the current charter,
        defeating SPEC Section 9 deep confirmation. FREEZE now persists the
        successor's hash and refuses any other successor.

        This test asks each honest witness to freeze for successor A and then
        for a DIFFERENT successor B; it asserts the second freeze is refused.
        """
        from sigil.charter import charter_body, charter_hash, quorum
        from sigil.crypto import verify

        net = Network()
        X = net.create_constellation("orion", 4)
        ws = net.witnesses(X)
        cur = net.registry.charter(X, 0)
        ch = charter_hash(cur)
        cA = charter_body("orion", 1, [KeyPair.generate().pk for _ in range(4)], ch)
        cB = charter_body("orion", 1, [KeyPair.generate().pk for _ in range(4)], ch)

        second_refused = 0
        sigsB = {}
        for w in ws:
            w.freeze(cA)                       # commit to successor A
            try:
                sigsB[w.pk], _ = w.freeze(cB)  # a DIFFERENT successor must be refused
            except Rejected:
                second_refused += 1
        members = set(cur["witnesses"])
        okB = sum(verify(pk, "charter", cB, s) for pk, s in sigsB.items() if pk in members)
        # Correct behaviour: every second freeze refused, so B never reaches a quorum.
        self.assertTrue(second_refused == len(ws) and okB < quorum(4),
                        "honest witnesses signed a second, conflicting successor charter")


if __name__ == "__main__":
    unittest.main()
