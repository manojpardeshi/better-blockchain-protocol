"""Code-to-model conformance for succession: the real ``Witness``, ``Standby``
and ``Network`` against ``formal/SigilSuccProofs.tla``.

WHAT THIS CHECKS
----------------
``formal/SigilSuccProofs.tla`` proves SPEC §8 safety under rotation and
succession for unbounded sizes. This test drives the REAL code under randomised
adversarial schedules and asserts, after every step, the model's succession
invariants and its safety theorems on the concrete state:

* the adversary is the owner (it signs every header in a pool over three
  sigils, generations 0..1), a Byzantine witness in version 0 (votes anything;
  its votes are eager, as in the model), and a Byzantine standby member in
  every committee (acknowledges anything without storing it, signs any
  successor at once, hands over an empty mirror);
* it collects mirror acks from any standby members of any version, keeps them
  forever and replays them later (also after a succession);
* it drives spends at current AND retired members (an old quorum that comes
  back), releases with assembled death proofs, heartbeat probes, clock jumps,
  crashes, cooperative rotations and dead-man takeovers.

REFINEMENT MAPPING (abstract  <-  concrete)
-------------------------------------------
    mir[v][m][s]   <-  bindings ``authorises`` accepts in Standby.mirror[s] of
                       the honest standby object of key m for version v
    fz[v]          <-  honest standby objects of v with ``fenced_for`` set
    sa[v]          <-  honest standby objects of v (they enter standby when created)
    hev[v][w][s]   <-  bind entries of w.records[s].log (logs only grow)
    votes          <-  every vote in every honest witness object (current and
                       retired), plus the Byzantine members' eager votes

Checked after every step:

* ``MirVotes``: behind every honest vote of a version with a committee, the
  honest standby members of that version that stored its binding, plus the
  committee's Byzantine members, reach the committee quorum (MirQ);
* fence: a standby member's mirror never changes once it signed a successor
  (MirrorAck requires ~fenced);
* inheritance (``InheritVote``): every honest member of a later version holds,
  in its adopted evidence, the binding behind every seal of an earlier version;
* ``HonestNoEquiv`` per key across all versions and processes;
* ``OneSealAcrossVersions`` and ``Safety`` (SPEC §8) over all votes.

Mutation tests: a witness that ignores mirror acks, and a standby member that
keeps storing after it fenced, are both caught.

Scale with SIGIL_SUCC_SEEDS / SIGIL_SUCC_STEPS.
"""

import os
import random
import unittest
from unittest import mock

from sigil import KeyPair, Network, locks, model
from sigil.charter import quorum, sign_charter
from sigil.proofs import verify_seal
from sigil.succession import Standby
from sigil.witness import CONTESTED, Conflict, Rejected, Witness, authorises
from tests.adversary import Equivocator

SEEDS = int(os.environ.get("SIGIL_SUCC_SEEDS", "25"))
STEPS = int(os.environ.get("SIGIL_SUCC_STEPS", "45"))
DEAD = 100


class ModelViolation(AssertionError):
    """The real code left a state the succession model forbids."""


class ByzStandby(Standby):
    """Acknowledges anything without storing it; signs any successor; empty handover."""

    def mirror_bind(self, req):
        auth = {k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}
        b = authorises(req.get("sigil"), auth)
        if b is None:
            raise Rejected("malformed")
        a = {"constellation": self.cid, "version": req.get("version"), "member": self.pk,
             "sigil": req["sigil"], "gen": b[0], "tid": b[1]}
        a["sig"] = self.kp.sign("mirror", model.ack_payload(a))
        return a

    def succeed(self, next_charter, sigs=None):
        return sign_charter(self.kp, next_charter), {}


class World:
    def __init__(self, rng: random.Random):
        self.rng = rng
        self.net = Network()
        self.owner = KeyPair.generate()
        self.exp = int(self.net.clock()) + 10 ** 9
        ck = [KeyPair.generate() for _ in range(4)]
        self.X = self.net.create_constellation("home", 4, byzantine={3: Equivocator},
                                               successor={"keys": ck, "dead_man": DEAD})
        self._byz_standby(0)
        self.byz_members = {0: self.net.all_witnesses(self.X)[3]}    # version -> Byzantine witness
        self.parcels = {}
        for salt in ("s", "x", "y"):
            p = model.parcel(self.X, "a", 1, locks.sig(self.owner.pk), salt)
            self.parcels[model.sigil_of(p)] = p
        sig = list(self.parcels)
        self.pool = []
        for k in range(7):
            ins = rng.sample(sig, rng.randint(1, 2))
            h = {"inputs": [[s, rng.randint(0, 1)] for s in ins], "body": f"{k:064x}"}
            self.pool.append((h, model.transition_id(h)))
        self.acks: dict[tuple, dict] = {}      # (version, sigil, gen, tid) -> {member: ack}
        self.fence_snap: dict[int, dict] = {}  # id(standby) -> its mirror when it fenced
        self.events = {"votes": 0, "late": 0, "takeovers": 0, "rotations": 0, "releases": 0}

    # ------------------------------------------------------------- helpers

    def _byz_standby(self, version):
        ms = self.net.committees[self.X]
        if not ms:
            return
        b = ByzStandby(ms[-1].kp, self.net.registry, self.net.clock)
        b.cid, b.version, b.since = self.X, version, int(self.net.clock())
        ms[-1] = b

    def standbys(self):
        return [m for m in self.net.committees.get(self.X, []) + self.net.retired_committees.get(self.X, [])]

    def witnesses(self):
        return [w for w in self.net.all_witnesses(self.X) + self.net.retired.get(self.X, [])
                if not isinstance(w, Equivocator)]

    def req(self, h, tid, s):
        p = self.parcels[s]
        u = locks.empty_unlock(self.exp)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, s, tid, self.exp)
        return {"sigil": s, "header": h, "home": self.X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def version(self):
        return self.net.registry.latest(self.X)["version"]

    # ------------------------------------------------------------- actions

    def act(self):
        r = self.rng.random()
        if r < 0.30:
            self.pay()
        elif r < 0.45:
            self.mirror()
        elif r < 0.65:
            self.spend()
        elif r < 0.76:
            self.release()
        elif r < 0.82:
            self.net.clock.advance(self.rng.choice([1, DEAD // 2, DEAD + 1]))
            self.probe()
        elif r < 0.88:
            self.toggle()
        elif r < 0.95:
            self.takeover()
        else:
            self.rotate()

    def pay(self):
        """Mirror a binding at the current committee, then ask current members to vote."""
        h, tid = self.rng.choice(self.pool)
        s, g = self.rng.choice(h["inputs"])
        v = self.version()
        r = dict(self.req(h, tid, s), version=v)
        for m in self.net.committee(self.X):
            try:
                a = m.mirror_bind(r)
            except Rejected:
                continue
            self.acks.setdefault((v, s, a["gen"], a["tid"]), {})[a["member"]] = a
        for _ in range(self.rng.randint(1, 4)):
            self.spend(choice=(h, tid, s, g), current=True)

    def mirror(self):
        h, tid = self.rng.choice(self.pool)
        s, g = self.rng.choice(h["inputs"])
        vs = sorted({m.version for m in self.standbys() if m.version is not None})
        if not vs:
            return
        v = self.rng.choice(vs)
        r = dict(self.req(h, tid, s), version=v)
        for m in self.standbys():
            if m.version == v and m.pk not in self.net.down and self.rng.random() < 0.8:
                try:
                    a = m.mirror_bind(r)
                except Rejected:
                    continue
                self.acks.setdefault((v, s, a["gen"], a["tid"]), {})[a["member"]] = a

    def spend(self, choice=None, current=False):
        cur = [w for w in self.net.all_witnesses(self.X) if not isinstance(w, Equivocator)]
        old = [w for w in self.witnesses() if w not in cur]
        group = old if (old and not current and self.rng.random() < 0.5) else cur
        ws = [w for w in group if w.pk not in self.net.down and w.cid is not None]
        if not ws:
            return
        w = self.rng.choice(ws)
        h, tid, s, g = choice or (lambda ht: (ht[0], ht[1], *self.rng.choice(ht[0]["inputs"])))(self.rng.choice(self.pool))
        held = list(self.acks.get((w.version, s, g, tid), {}).values())
        self.rng.shuffle(held)
        if held and self.rng.random() < 0.2:
            held = held[: self.rng.randint(0, len(held))]
        r = dict(self.req(h, tid, s), mirror=held)
        before = w.records.get(s)
        b = (before.gen, before.tid, before.abstain) if before else (0, None, False)
        n = len(before.votes) if before else 0
        try:
            w.spend(r)
        except (Rejected, Conflict):
            return
        rec = w.records[s]
        if len(rec.votes) > n:
            v = rec.votes[-1]
            g0, t0, ab = b
            if not ((v["gen"] == g0 and t0 in (None, v["tid"])) or (v["gen"] > g0 and t0 is None)):
                raise ModelViolation(f"Spend precondition: vote at {v['gen']} from ({g0},{t0})")
            if ab and v["gen"] == g0:
                raise ModelViolation("an abstaining record voted")
            self.events["votes"] += 1
            if w not in self.net.all_witnesses(self.X):
                self.events["late"] += 1

    def release(self):
        ws = [w for w in self.witnesses() if w.pk not in self.net.down and w.cid is not None]
        if not ws:
            return
        w = self.rng.choice(ws)
        bound = [(s, rec) for s, rec in w.records.items() if rec.tid is not None]
        if not bound:
            return
        s, rec = self.rng.choice(bound)
        cands = [(c[1], c[2]) for c in rec.candidates] if rec.tid == CONTESTED else [(rec.tid, rec.header)]
        for tid, header in cands:
            for proof in self.death_proofs(header, tid):
                try:
                    w.release(s, proof)
                    self.events["releases"] += 1
                    return
                except Rejected:
                    continue

    def death_proofs(self, header, tid):
        out = []
        for s, g in header["inputs"]:
            p = self.parcels[s]
            target = {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
            for (ver, tt), vs in self.votes_at(s, g).items():
                if tt != tid:
                    out.append({"kind": "seal", "sigil": s, "gen": g, "parcel": target,
                                "seal": model.seal_from_votes(list(vs.values()))})
        return out

    def votes_at(self, s, g):
        """{(version, tid): {witness: vote}} with honest votes and eager Byzantine ones."""
        out: dict[tuple, dict] = {}
        for w in self.witnesses():
            rec = w.records.get(s)
            for v in (rec.votes if rec else []):
                if v["gen"] == g:
                    out.setdefault((v["version"], v["tid"]), {})[v["witness"]] = v
        for ver, b in self.byz_members.items():
            for h, tid in self.pool:
                if [s, g] in h["inputs"]:
                    b.version = ver
                    out.setdefault((ver, tid), {})[b.pk] = b.forge(s, g, tid)
        return out

    def probe(self):
        for m in self.net.committee(self.X):
            m.probe([w for w in self.net.witnesses(self.X) if self.rng.random() < 0.7])

    def toggle(self):
        objs = self.net.all_witnesses(self.X) + self.net.committees.get(self.X, [])
        if objs:
            o = self.rng.choice(objs)
            self.net.down.symmetric_difference_update({o.pk})

    def takeover(self):
        if self.net.registry.latest(self.X).get("successor") is None or self.version() >= 3:
            return
        self.net.clock.advance(DEAD + 1)
        if self.rng.random() < 0.5:
            self.probe()                             # maybe the home is alive: then no takeover
        succ = {"n": 4, "dead_man": DEAD} if self.rng.random() < 0.7 else None
        try:
            v = self.net.succeed(self.X, [KeyPair.generate() for _ in range(4)], successor=succ)
        except RuntimeError:
            return
        self._byz_standby(v)
        self.events["takeovers"] += 1

    def rotate(self):
        if self.version() >= 3:
            return
        succ = {"n": 4, "dead_man": DEAD} if self.rng.random() < 0.7 else None
        try:
            v = self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)], successor=succ)
        except RuntimeError:
            return
        self._byz_standby(v)
        self.events["rotations"] += 1

    # ------------------------------------------------------------- checks

    def stored(self, m, s, g, tid) -> bool:
        return any(e.get("kind") == "bind" and authorises(s, e.get("auth", {})) == (g, tid)
                   for e in m.mirror.get(s, []))

    def check(self):
        reg = self.net.registry
        # Fence: a fenced standby member's mirror never changes.
        for m in self.standbys():
            if isinstance(m, ByzStandby) or m.fenced_for is None:
                continue
            snap = self.fence_snap.setdefault(id(m), m.snapshot())
            if m.snapshot() != snap:
                raise ModelViolation(f"standby {m.pk[:8]} stored after it fenced")
        # MirVotes, and HonestNoEquiv per key across all its processes.
        by_key: dict[tuple, str] = {}
        for w in self.witnesses():
            for s, rec in w.records.items():
                for v in rec.votes:
                    k = (w.pk, s, v["gen"])
                    if by_key.setdefault(k, v["tid"]) != v["tid"]:
                        raise ModelViolation(f"HonestNoEquiv: {w.pk[:8]} voted two tids at ({s[:8]},{v['gen']})")
                    committee = reg.committee(self.X, v["version"])
                    if committee is None:
                        continue
                    honest = {m.pk for m in self.standbys() if not isinstance(m, ByzStandby)
                              and m.version == v["version"] and m.pk in committee
                              and self.stored(m, s, v["gen"], v["tid"])}
                    byz = {m.pk for m in self.standbys() if isinstance(m, ByzStandby)
                           and m.version == v["version"] and m.pk in committee}
                    if len(honest | byz) < quorum(len(committee)):
                        raise ModelViolation(f"MirVotes: vote of v{v['version']} at ({s[:8]},{v['gen']}) "
                                             f"behind only {len(honest)} honest standby members")
        # Seals across versions: Lemma 1, Safety, and inheritance by later members.
        sealed = {}
        for s in self.parcels:
            for g in (0, 1):
                for (ver, tid), vs in self.votes_at(s, g).items():
                    if verify_seal(model.seal_from_votes(list(vs.values())), reg):
                        sealed.setdefault((s, g), {})[tid] = ver
        for (s, g), tids in sealed.items():
            if len(tids) > 1:
                raise ModelViolation(f"two seals at ({s[:8]},{g}): {sorted(tids)}")
        complete = {}
        for h, tid in self.pool:
            if all(tid in sealed.get((s, g), {}) for s, g in h["inputs"]):
                for s, _ in h["inputs"]:
                    complete.setdefault(s, set()).add(tid)
        for s, tids in complete.items():
            if len(tids) > 1:
                raise ModelViolation(f"double consumption of {s[:8]}: {tids}")
        for w in self.net.all_witnesses(self.X):
            if isinstance(w, Equivocator) or w.cid is None:
                continue
            for (s, g), tids in sealed.items():
                for tid, ver in tids.items():
                    if ver < w.version and not any(
                            e.get("kind") == "bind" and authorises(s, e.get("auth", {})) == (g, tid)
                            for e in (w.records[s].log if s in w.records else [])):
                        raise ModelViolation(f"v{w.version} member misses the seal of v{ver} at ({s[:8]},{g})")


class SuccessionConformanceTests(unittest.TestCase):
    def run_worlds(self, seeds, steps):
        totals: dict[str, int] = {}
        for seed in range(seeds):
            world = World(random.Random(seed))
            for _ in range(steps):
                world.act()
                world.check()
            for k, v in world.events.items():
                totals[k] = totals.get(k, 0) + v
        return totals

    def test_real_code_refines_the_succession_model(self):
        totals = self.run_worlds(SEEDS, STEPS)
        # Non-vacuity: the schedules really take over, rotate, vote late and release.
        self.assertGreater(totals["takeovers"], 0, totals)
        self.assertGreater(totals["rotations"], 0, totals)
        self.assertGreater(totals["late"], 0, totals)
        self.assertGreater(totals["votes"], 0, totals)

    def test_detects_a_witness_that_ignores_mirror_acks(self):
        def everyone(acks, committee, *a):
            return set(committee)
        with mock.patch("sigil.witness.acked_by", everyone):
            with self.assertRaises(ModelViolation):
                self.run_worlds(SEEDS, STEPS)

    def test_detects_a_standby_member_that_stores_after_fencing(self):
        def active(self):
            if self.cid is None:
                raise Rejected("not standing by")
        with mock.patch.object(Standby, "_active", active):
            with self.assertRaises(ModelViolation):
                self.run_worlds(SEEDS, STEPS)


if __name__ == "__main__":
    unittest.main()
