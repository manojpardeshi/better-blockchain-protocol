"""Randomised model checking of the safety property across charter
rotations and across two constellations.

This extends ``tests/test_model_check.py`` (one constellation, one charter
version) along two dimensions. The property is the same:

    SAFETY: no sigil is consumed by two different *complete* transitions.

Now a transition is complete when every input ``[s, g]`` has a valid seal
for ``(s, g, tid)`` from **any charter version** of ``s``'s home
constellation. Holders accept a seal from any version (SPEC §6.4), so a
seal formed by votes that were cast before a rotation, by witnesses that
are now frozen, still counts.

Adversary, per constellation and per charter version:

* exactly one Byzantine member, which signs any vote for anything (its
  vote is added to every seal and every death proof we assemble);
* the owner of every sigil, who authorises every transition of a pool of
  overlapping, conflicting transitions at random generations, and during
  the run signs fresh ones at the generations witnesses currently use
  (including plain double-spend attempts on already-consumed sigils);
* the scheduler, which delivers spend requests to any honest witness (the
  home's current members, frozen ex-members, members that never froze,
  witnesses of the other constellation) and release requests carrying
  the strongest death proofs it can assemble from every vote ever cast,
  in any constellation and any version, including "pooled" vote sets that
  mix constellations or versions.

ROTATION (``rotations > 0``): at random steps a constellation rotates to a
new charter version, mirroring ``Network.rotate`` but adversarially: a
random signing quorum of the old version (2 or 3 honest members, plus the
Byzantine one when needed) freezes; old honest members outside the quorum
stay *unfrozen* in the old version and keep voting there (at most f of
them, as SPEC §8 allows). The new version has 3 honest members (fresh keys
or re-used keys of honest signers) and one Byzantine member (fresh or the
old Byzantine key). Each new honest member adopts the snapshots of a
random quorum-sized subset of the signers (a re-used member always
includes its own). The Byzantine signer hands the new members one forged
snapshot, or a different one each: a real log with entries dropped;
claims that every sealed transition was released; or random edits
(bindings validly authorised by the adversarial owner, bindings with
broken authorisations, releases backed by the strongest available death
proofs, releases with bogus proofs, junk).

TWO CONSTELLATIONS (``n_const == 2``): sigils are homed in either
constellation, pool transitions mix inputs across them, and death proofs
for a binding in one constellation cite seals and votes of the other.

The explorers also check that frozen witnesses reject every request and
never sign again. Mutation tests break one rule each and require the
explorer to find a double spend.

ROGUE (``rogue=True``, off by default): adds a third, fully Byzantine
constellation to the shared registry. This breaks the per-constellation
fault assumption of SPEC §8, but creating a constellation is
permissionless and the reference ``Network`` keeps one shared registry.
See ``KnownGapTests``.

Scale with SIGIL_MODEL_EXT_SEEDS / SIGIL_MODEL_STEPS.
"""

import os
import random
import unittest
from collections import defaultdict
from unittest import mock

from sigil import KeyPair, Network, Wallet, locks, model
from sigil.charter import charter_body, charter_hash, quorum, sign_charter
from sigil.proofs import verify_equivocation, verify_seal
from sigil.wallet import request_seal
from sigil.witness import CONTESTED, Rejected, Witness
from tests import test_model_check as base

SEEDS = int(os.environ.get("SIGIL_MODEL_EXT_SEEDS", str(max(1, base.SEEDS // 4))))
STEPS = base.STEPS
N = 4
Q = quorum(N)


class FrozenWitnessVoted(AssertionError):
    pass


class Universe:
    def __init__(self, rng: random.Random, *, n_const=1, rotations=0, steps=STEPS,
                 n_sigils=4, pool=8, max_gen=2, rogue=False):
        self.rng = rng
        self.net = Network()
        self.reg = self.net.registry
        self.cids = []
        self.version = {}                    # cid -> current charter version
        self.current = {}                    # cid -> current-version honest witnesses
        self.honest = defaultdict(list)      # cid -> every honest witness object ever (all versions)
        self.byz = {}                        # (cid, version) -> [Byzantine witness objects]
        for c in range(n_const):
            cid = self.net.create_constellation(f"c{c}", N)
            ws = self.net.witnesses(cid)
            self.cids.append(cid)
            self.version[cid] = 0
            self.current[cid] = ws[:3]
            self.honest[cid] = list(ws[:3])
            self.byz[(cid, 0)] = [ws[3]]
        if rogue:
            rid = self.net.create_constellation("rogue", N)
            self.byz[(rid, 0)] = self.net.witnesses(rid)
        self.owner = KeyPair.generate()
        self.parcels, self.home = {}, {}
        for i in range(n_sigils):
            cid = self.cids[i % n_const]
            p = model.parcel(cid, "x", 1, locks.sig(self.owner.pk), f"salt{i}")
            s = model.sigil_of(p)
            self.parcels[s], self.home[s] = p, cid
        sigils = list(self.parcels)
        self.pool = []
        self.max_pool = 2 * pool
        by_home = defaultdict(list)
        for x in sigils:
            by_home[self.home[x]].append(x)
        for k in range(pool):
            if n_const > 1 and k % 2 == 0:
                # Every other transition spans both constellations.
                ins = [rng.choice(by_home[c]) for c in self.cids]
                ins += rng.sample([x for x in sigils if x not in ins], rng.randint(0, 1))
            else:
                ins = rng.sample(sigils, rng.randint(1, min(3, len(sigils))))
            h = {"inputs": [[s, rng.randint(0, max_gen)] for s in ins], "body": f"{k:064x}"}
            self.pool.append((h, model.transition_id(h)))
        self.rotate_at = set(rng.sample(range(steps), min(rotations, steps)))
        self.focus = rng.choice(self.pool)  # the transition the scheduler currently pushes
        self.t = 0
        self.stats = defaultdict(int)
        self._idx = None

    # ------------------------------------------------------------ helpers

    def all_honest(self):
        return [w for cid in self.cids for w in self.honest[cid]]

    def auth(self, header, tid, sigil):
        p = self.parcels[sigil]
        u = locks.empty_unlock()
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, tid)
        return {"home": p["home"], "lock": p["lock"], "salt": p["salt"], "unlock": u, "header": header}

    def request(self, header, tid, sigil):
        return dict(self.auth(header, tid, sigil), sigil=sigil)

    def index(self):
        """(sigil, gen) -> (cid, version) -> tid -> {witness: vote}, over every honest vote ever cast."""
        if self._idx is None:
            idx = defaultdict(lambda: defaultdict(lambda: defaultdict(dict)))
            for w in self.all_honest():
                for s, rec in w.records.items():
                    for v in rec.votes:
                        idx[(s, v["gen"])][(v["constellation"], v["version"])][v["tid"]][v["witness"]] = v
            self._idx = idx
        return self._idx

    def seal_versions(self, s, g, tid):
        """Charter versions of s's home in which (s, g, tid) has a quorum (Byzantine vote included)."""
        cid = self.home[s]
        groups = self.index().get((s, g), {})
        out = []
        for ver in range(self.version[cid] + 1):
            n = len(groups.get((cid, ver), {}).get(tid, {})) + len(self.byz[(cid, ver)])
            if n >= Q:
                out.append(ver)
        return out

    def complete(self, header, tid):
        return all(self.seal_versions(s, g, tid) for s, g in header["inputs"])

    def death_proofs(self, header, tid):
        """Every death proof the adversary can assemble against ``tid``."""
        proofs = []
        idx = self.index()
        fake = "f" * 64
        for s, g in header["inputs"]:
            p = self.parcels[s]
            target = {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
            groups = idx.get((s, g), {})
            pooled = {}
            for key, byz in self.byz.items():
                by_tid = groups.get(key, {})
                others = {}
                for t, vs in by_tid.items():
                    if t != tid:
                        votes = list(vs.values()) + [b._vote(s, g, t) for b in byz]
                        proofs.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target, "seal": model.seal_from_votes(votes)})
                        others.update(vs)
                votes = list(others.values()) + [b._vote(s, g, fake) for b in byz]
                proofs.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target,
                               "seal": model.seal_from_votes([b._vote(s, g, fake) for b in byz])})
                proofs.append({"kind": "votes", "sigil": s, "gen": g, "parcel": target, "votes": votes})
                pooled.update({(v["constellation"], v["version"], v["witness"]): v for v in votes})
            # Votes mixed across constellations / versions: must never be counted together.
            mixed = list(pooled.values())
            self.rng.shuffle(mixed)
            proofs.append({"kind": "votes", "sigil": s, "gen": g, "parcel": target, "votes": mixed})
        return proofs

    # ---------------------------------------------------------- rotation

    def forge_snapshot(self, cid):
        """What the Byzantine signer hands one new member.

        Three strategies: *omit* (a real log with entries dropped), *kill*
        (claim that every sealed transition was released) and *mixed*
        (random edits of every kind).
        """
        rng = self.rng
        mode = rng.choice(["omit", "kill", "mixed"])
        snap = {}
        if mode == "omit" or rng.random() < 0.7:
            src = rng.choice(self.current[cid])
            snap = {s: [e for e in r.log if rng.random() < 0.7] for s, r in src.records.items() if rng.random() < 0.6}
        if mode == "omit":
            return snap
        sealed = [(h, t) for h, t in self.pool
                  if any(self.home[x] == cid and self.seal_versions(x, g, t) for x, g in h["inputs"])]
        bound = [(r.header, r.tid) for w in self.current[cid] for r in w.records.values()
                 if r.tid not in (None, CONTESTED)]
        b = self.byz[(cid, self.version[cid])][0]

        def release(h, t, s, g, strongest):
            proof = (rng.choice(self.death_proofs(h, t)) if strongest else
                     {"kind": "seal", "sigil": s, "gen": g, "seal": model.seal_from_votes([b._vote(s, g, "f" * 64)])})
            return {"kind": "release", "gen": g, "tid": t, "header": h, "proof": proof}

        if mode == "kill":
            for h, t in sealed:
                s, g = rng.choice([[x, g] for x, g in h["inputs"] if self.home[x] == cid] or h["inputs"])
                snap.setdefault(s, []).append(release(h, t, s, g, rng.random() < 0.5))
            return snap
        for _ in range(rng.randint(1, 4)):
            targets = sealed + bound
            h, t = rng.choice(targets) if targets and rng.random() < 0.6 else rng.choice(self.pool)
            s, g = rng.choice(h["inputs"])
            r = rng.random()
            if r < 0.15:     # a binding the owner really authorised (but no honest witness may have seen)
                e = {"kind": "bind", "gen": g, "auth": self.auth(h, t, s)}
            elif r < 0.3:    # a binding with a broken authorisation
                a = self.auth(h, t, s)
                a["unlock"] = locks.empty_unlock()
                e = {"kind": "bind", "gen": g, "auth": a}
            elif r < 0.4:    # authorisation re-labelled to another header
                a = self.auth(h, t, s)
                a["header"] = dict(h, body="e" * 64)
                e = {"kind": "bind", "gen": g, "auth": a}
            elif r < 0.7:    # a release backed by the strongest proof available
                e = release(h, t, s, g, True)
            elif r < 0.95:   # a release with a proof only the Byzantine member signed
                e = release(h, t, s, g, False)
            else:
                e = {"kind": rng.choice(["bind", "release", "junk"]), "gen": 99}
            snap.setdefault(s, []).append(e)
        return snap

    def rotate(self, cid):
        rng = self.rng
        v = self.version[cid]
        old_honest, old_byz = self.current[cid], self.byz[(cid, v)][0]
        # A random signing quorum of the old version freezes; honest members
        # outside it stay unfrozen in the old version (at most f of them).
        signers = rng.sample(old_honest, rng.choice([2, 3]))
        byz_signs = len(signers) < Q or rng.random() < 0.75
        # Honest members re-used in the new version are ones that froze
        # (an unfrozen old member keeps voting in the old version).
        keep = rng.sample(signers, rng.randint(0, len(signers)))
        new_honest_keys = [w.kp for w in keep] + [KeyPair.generate() for _ in range(3 - len(keep))]
        new_byz_key = old_byz.kp if rng.random() < 0.5 else KeyPair.generate()
        members = [k.pk for k in new_honest_keys] + [new_byz_key.pk]
        rng.shuffle(members)
        cur = self.reg.charter(cid, v)
        nxt = charter_body(cur["name"], v + 1, members, charter_hash(cur))

        sigs, snaps = {}, {}
        for w in signers:
            sig, snap = w.freeze(nxt)
            sigs[w.pk] = sig
            snaps[w.pk] = snap
        if byz_signs:
            sigs[old_byz.pk] = sign_charter(old_byz.kp, nxt)
            snaps[old_byz.pk] = None  # placeholder for the Byzantine snapshot
        # The Byzantine signer either tells every new member the same lie or
        # a different lie to each.
        shared = self.forge_snapshot(cid) if rng.random() < 0.5 else None
        self.reg.add_chain(cid, self.reg.chain(cid) + [{"body": nxt, "sigs": sigs}])

        new = []
        for kp in new_honest_keys:
            # Each new member hears from a random quorum of the signers; a
            # re-used member always remembers its own log.
            chosen = rng.sample(list(snaps), rng.randint(Q, len(snaps)))
            if kp.pk in snaps and kp.pk not in chosen:
                chosen.append(kp.pk)
            given = [snaps[pk] if snaps[pk] is not None
                     else (shared if shared is not None else self.forge_snapshot(cid)) for pk in chosen]
            w = Witness(kp, self.reg, self.net.clock)
            w.adopt(cid, v + 1, given)
            self.stats["contested"] += sum(1 for r in w.records.values() if r.tid == CONTESTED)
            self.stats["inherited"] += sum(1 for r in w.records.values() if r.tid not in (None, CONTESTED))
            new.append(w)
        b = Witness(new_byz_key, self.reg, self.net.clock)
        b.join(cid, v + 1)
        self.version[cid] = v + 1
        self.current[cid] = new
        self.honest[cid].extend(new)
        self.byz[(cid, v + 1)] = [b]
        self.net.members[cid] = new + [b]
        self.stats["rotations"] += 1
        self._idx = None

    # -------------------------------------------------------------- steps

    def _deliver(self, w, fn):
        """Run one request against honest witness ``w``; frozen witnesses must refuse and stay silent."""
        frozen = w.frozen
        before = sum(len(r.votes) for r in w.records.values())
        try:
            out = fn()
        except Rejected:
            out = None
        finally:
            self._idx = None
        if frozen:
            if out is not None or sum(len(r.votes) for r in w.records.values()) != before:
                raise FrozenWitnessVoted(f"frozen witness {w.pk[:8]} acted")
            self.stats["frozen_refusals"] += 1
        return out

    def step(self):
        rng = self.rng
        if self.t in self.rotate_at:
            self.rotate(rng.choice(self.cids))
        self.t += 1
        if rng.random() < 0.05:
            self.focus = rng.choice(self.pool)
        if rng.random() < 0.04 and len(self.pool) < self.max_pool:
            self.adapt()
        if rng.random() < 0.65:
            header, tid = self.focus if rng.random() < 0.5 else rng.choice(self.pool)
            s, _ = rng.choice(header["inputs"])
            home = self.home[s]
            w = rng.choice(self.honest[home] if rng.random() < 0.9 else self.all_honest())
            n_votes = len(w.status(s)["votes"])
            self._deliver(w, lambda: w.spend(self.request(header, tid, s)))
            if (w.cid == home and w.version < self.version[home]
                    and len(w.status(s)["votes"]) > n_votes):
                self.stats["stale_version_votes"] += 1   # an unfrozen ex-member still voting
        else:
            bound = [(w, s, r) for w in self.all_honest() for s, r in w.records.items()
                     if r.tid not in (None, CONTESTED)]
            if not bound:
                return
            w, s, rec = rng.choice(bound)
            proofs = self.death_proofs(rec.header, rec.tid)
            rng.shuffle(proofs)
            for proof in proofs:
                if self._deliver(w, lambda: w.release(s, proof)) is not None:
                    self.stats["releases"] += 1
                    src = proof["seal"] if proof["kind"] == "seal" else proof["votes"][0]
                    if src["constellation"] != w.cid:
                        self.stats["cross_releases"] += 1
                    if src["version"] != w.version:
                        self.stats["cross_version_releases"] += 1
                    break
                if w.frozen:
                    break

    def adapt(self):
        """The owner signs a fresh transition at generations the witnesses are using now."""
        rng = self.rng
        sigils = list(self.parcels)
        consumed = {x for h, t in self.pool if self.complete(h, t) for x, _ in h["inputs"]}
        spent = [x for x in sigils if x in consumed]  # parcel order keeps runs reproducible
        if spent and rng.random() < 0.5:
            ins = [rng.choice(spent)]   # a plain double-spend attempt on an already-consumed sigil
        else:
            ins = rng.sample(sigils, rng.randint(1, min(3, len(sigils))))
        inputs = []
        for x in ins:
            gens = {w.status(x)["gen"] for w in self.honest[self.home[x]] if not w.frozen}
            inputs.append([x, rng.choice(sorted(gens | {0}))])
        h = {"inputs": inputs, "body": f"{len(self.pool):064x}"}
        self.pool.append((h, model.transition_id(h)))
        self.focus = self.pool[-1]
        self.stats["adaptive_transitions"] += 1

    def violation(self):
        for s in self.parcels:
            done = {tid for h, tid in self.pool if any(x == s for x, _ in h["inputs"]) and self.complete(h, tid)}
            if len(done) > 1:
                return s, done
        n = self.honest_key_equivocations()
        if n:
            return "honest key equivocated", n  # an honest witness could be framed and slashed
        return None

    def honest_key_equivocations(self):
        """Pairs of votes by one honest key with the same (constellation, sigil, gen) and different tids.

        SPEC §5.1 forbids this and §3.8 makes it a valid equivocation proof
        (which is not scoped to a charter version), so it is checked as a
        violation alongside double spends.
        """
        seen, out = {}, 0
        for w in self.all_honest():
            for s, rec in w.records.items():
                for v in rec.votes:
                    k = (v["witness"], v["constellation"], s, v["gen"])
                    if k in seen and seen[k] != v["tid"]:
                        out += 1
                    seen.setdefault(k, v["tid"])
        return out

    def final_stats(self):
        if self.honest_key_equivocations():
            self.stats["runs_with_honest_key_equivocation"] += 1
        for h, t in self.pool:
            if not self.complete(h, t):
                continue
            self.stats["completions"] += 1
            if len({self.home[s] for s, _ in h["inputs"]}) > 1:
                self.stats["cross_completions"] += 1
            vers = [(self.home[s], self.seal_versions(s, g, t)) for s, g in h["inputs"]]
            if any(max(vs) > 0 for _, vs in vers):
                self.stats["completions_new_version"] += 1
            if any(max(vs) < self.version[cid] for cid, vs in vers):
                self.stats["completions_old_version"] += 1  # relies on votes of a retired version


def explore(seeds, steps, **kw):
    """Return (seed, violation, stats); seed is None if no violation was found."""
    stats = defaultdict(int)
    for seed in range(seeds):
        u = Universe(random.Random(seed), steps=steps, **kw)
        for _ in range(steps):
            u.step()
            bad = u.violation()
            if bad:
                return seed, bad, dict(stats)
        u.final_stats()
        for k, v in u.stats.items():
            stats[k] += v
    stats["seeds"] = seeds
    return None, None, dict(stats)


# ------------------------------------------------------------- mutations

def adopt_ignores_evidence():
    """New members start with blank records: inherited bindings are lost."""
    return [mock.patch.object(Witness, "adopt", lambda self, cid, version, snaps: self.join(cid, version))]


def adopt_trusts_release_entries():
    """ADOPT believes every handed-over release without checking its death proof."""
    real_adopt = Witness.adopt
    real_pd = Witness.adopt.__globals__["proves_dead"]
    state = {"adopting": False}

    def adopt(self, *a):
        state["adopting"] = True
        try:
            return real_adopt(self, *a)
        finally:
            state["adopting"] = False

    def pd(*a):
        return True if state["adopting"] else real_pd(*a)

    return [mock.patch.object(Witness, "adopt", adopt), mock.patch("sigil.witness.proves_dead", pd)]


def votes_pooled_across_charters():
    """Death-proof votes are counted per signer's own charter, so votes from
    different constellations / versions add up to a quorum."""
    import sigil.proofs as proofs

    def counted(votes, registry, convicted=frozenset()):
        out, first = set(), None
        for v in votes:
            ch = registry.charter(v["constellation"], v["version"])
            if ch is None:
                continue
            first = first or ch
            if v["witness"] in ch["witnesses"] and proofs.verify_vote(v):
                out.add((v["constellation"], v["version"], v["witness"]))
        return out, first

    return [mock.patch("sigil.proofs._counted_witnesses", counted)]


def witness_skips_generation_check():
    """A witness votes at a generation below its record's (the stale check is gone)."""
    real = Witness.spend

    def spend(self, req):
        rec = self.records.get(req.get("sigil"))
        try:
            gen = next(g for s, g in req["header"]["inputs"] if s == req["sigil"])
        except (KeyError, TypeError, StopIteration):
            gen = None
        if rec is not None and isinstance(gen, int) and gen < rec.gen:
            saved = (rec.gen, rec.tid, rec.header, rec.vote)
            rec.gen, rec.tid, rec.header, rec.vote = gen, None, None, None
            try:
                return real(self, req)
            finally:
                rec.gen, rec.tid, rec.header, rec.vote = saved
        return real(self, req)

    return [mock.patch.object(Witness, "spend", spend)]


def run_mutated(patches, seeds, steps, **kw):
    for p in patches:
        p.start()
    try:
        return explore(seeds, steps, **kw)
    finally:
        for p in reversed(patches):
            p.stop()


# Mutation runs stop at the first violation, so a larger seed budget is cheap.
MUTATION_SEEDS = 3 * SEEDS

ROTATION = dict(n_const=1, rotations=2)
TWO = dict(n_const=2, rotations=0, n_sigils=5)
BOTH = dict(n_const=2, rotations=3, n_sigils=5)


class RotationModelCheck(unittest.TestCase):
    def test_no_double_spend_across_rotations(self):
        seed, bad, st = explore(SEEDS, STEPS, **ROTATION)
        self.assertIsNone(seed, f"double spend across rotation, seed {seed}: {bad}")
        self.assertEqual(st["rotations"], 2 * SEEDS)
        for k in ("releases", "completions", "completions_new_version", "completions_old_version",
                  "frozen_refusals", "inherited", "stale_version_votes", "cross_version_releases"):
            self.assertGreater(st[k], 0, f"exploration never exercised {k}: {st}")

    def test_checker_detects_adopt_ignoring_evidence(self):
        seed, _, _ = run_mutated(adopt_ignores_evidence(), MUTATION_SEEDS, STEPS, **ROTATION)
        self.assertIsNotNone(seed, "blank adoption should allow a double spend")

    def test_checker_detects_adopt_trusting_forged_releases(self):
        seed, _, _ = run_mutated(adopt_trusts_release_entries(), MUTATION_SEEDS, STEPS, **ROTATION)
        self.assertIsNotNone(seed, "believing forged releases should allow a double spend")


class TwoConstellationModelCheck(unittest.TestCase):
    def test_no_double_spend_across_constellations(self):
        seed, bad, st = explore(SEEDS, STEPS, **TWO)
        self.assertIsNone(seed, f"cross-constellation double spend, seed {seed}: {bad}")
        for k in ("releases", "completions", "cross_completions", "cross_releases"):
            self.assertGreater(st[k], 0, f"exploration never exercised {k}: {st}")

    def test_checker_detects_votes_pooled_across_charter_versions(self):
        # Pooling across *constellations* is also blocked by the home check in
        # proves_dead, so the mutation only bites across versions of one home.
        seed, _, _ = run_mutated(votes_pooled_across_charters(), MUTATION_SEEDS, STEPS, **ROTATION)
        self.assertIsNotNone(seed, "pooling votes across charter versions should allow a double spend")

    def test_checker_detects_skipped_generation_check(self):
        seed, _, _ = run_mutated(witness_skips_generation_check(), MUTATION_SEEDS, STEPS, **TWO)
        self.assertIsNotNone(seed, "voting at stale generations should allow a double spend")


class CombinedModelCheck(unittest.TestCase):
    def test_no_double_spend_with_rotations_in_two_constellations(self):
        seed, bad, st = explore(max(1, SEEDS // 2), STEPS, **BOTH)
        self.assertIsNone(seed, f"double spend, seed {seed}: {bad}")
        self.assertGreater(st["cross_completions"], 0)
        self.assertGreater(st["completions_new_version"], 0)


class KnownGapTests(unittest.TestCase):
    """Regression tests for two gaps the extended explorer found in v0 (both fixed).

    Gap 1 (safety). A death proof could cite *any* constellation in the
    witness's registry. Constellations are permissionless, so an attacker
    could register one it fully controls and "prove" that a *sealed*
    transition was dead; the honest home witnesses released it and sealed a
    second spend, and holders accepted both. Fixed: SPEC §3.9 death proofs
    reveal the target's ``{home, lock, salt}`` and the evidence must come
    from that home.

    Gap 2 (framing, not a double spend). ADOPT could re-bind a sigil at a
    generation where a re-used member's key had already voted for a
    transition since proven dead, so an honest witness signed two votes for
    one (constellation, sigil, gen): a valid §3.8 equivocation proof. Fixed:
    snapshots carry each witness's own votes and ADOPT abstains rather than
    vote a second tid at that generation (SPEC §5.4).
    """

    def test_rogue_constellation_cannot_kill_a_sealed_transition(self):
        net = Network()
        X = net.create_constellation("orion")             # 4 honest witnesses
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd = alice.issue("USD", 100)
        (ref,), _ = alice.select(usd, 100)
        p = alice.dossier.output(ref)
        s = model.sigil_of(p)
        key = alice.keys[p["lock"]["pk"]]

        def spend(gen, memo):
            b = bob.address()
            h = {"inputs": [[s, gen]], "body": model.body_hash(
                model.body([ref], [model.parcel(X, usd, 100, b["lock"], b["salt"])], memo=memo))}
            t = model.transition_id(h)
            u = locks.empty_unlock()
            u["sigs"][key.pk] = locks.sign_unlock(key, s, t)
            req = {"sigil": s, "header": h, "home": X, "lock": p["lock"], "salt": p["salt"], "unlock": u}
            return t, request_seal(net, req)

        t1, seal1 = spend(0, "to bob")
        rogue = net.create_constellation("rogue")         # attacker holds all four keys
        fake = model.seal_from_votes([w._vote(s, 0, "f" * 64) for w in net.witnesses(rogue)])
        proof = {"kind": "seal", "sigil": s, "gen": 0, "seal": fake}
        for w in net.witnesses(X):
            try:
                w.release(s, proof)
            except Rejected:
                pass
        try:
            t2, seal2 = spend(1, "to bob again")
        except Exception:
            return  # the second spend could not be sealed: safe
        both = (t1 != t2 and seal1["constellation"] == seal2["constellation"] == X
                and verify_seal(seal1, net.registry) and verify_seal(seal2, net.registry))
        self.assertFalse(both, "sigil sealed into two transitions at its home")

    def test_rotation_never_makes_an_honest_witness_equivocate(self):
        net = Network()
        X = net.create_constellation("orion")              # all four witnesses honest
        owner = KeyPair.generate()
        p = model.parcel(X, "x", 1, locks.sig(owner.pk), "salt")
        s = model.sigil_of(p)

        def req(name):
            h = {"inputs": [[s, 0]], "body": name * 64}
            u = locks.empty_unlock()
            u["sigs"][owner.pk] = locks.sign_unlock(owner, s, model.transition_id(h))
            return {"sigil": s, "header": h, "home": X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

        w0, w1, w2, w3 = net.witnesses(X)
        ra, rb, rc = req("a"), req("b"), req("c")          # the owner equivocates three ways
        va, vb = w0.spend(ra), w1.spend(rb)
        vc = [w2.spend(rc), w3.spend(rc)]
        # Neither A nor B can ever be sealed; their witnesses release honestly.
        target = {"home": X, "lock": p["lock"], "salt": p["salt"]}
        w0.release(s, {"kind": "votes", "sigil": s, "gen": 0, "parcel": target, "votes": [vb] + vc})
        w1.release(s, {"kind": "votes", "sigil": s, "gen": 0, "parcel": target, "votes": [va] + vc})
        net.rotate(X, [w.kp for w in (w0, w1, w2, w3)])  # same keys, next version
        try:
            again = net.witnesses(X)[0].spend(rc)         # adopted: bound to C at gen 0
        except Rejected:
            return                                        # abstains rather than signing C at gen 0
        self.assertFalse(verify_equivocation({"a": va, "b": again}),
                         "an honest witness was made to equivocate")

    def test_explorer_with_rogue_constellation(self):
        """The explorer finds the same gap on its own once a rogue constellation exists."""
        seed, bad, _ = explore(MUTATION_SEEDS, STEPS, rogue=True, **TWO)
        self.assertIsNone(seed, f"double spend via rogue constellation, seed {seed}: {bad}")


if __name__ == "__main__":
    unittest.main()
