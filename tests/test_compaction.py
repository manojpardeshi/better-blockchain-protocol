"""Settlement, checkpoints and delta dossiers (SPEC §3.12, §5.7, §6.1; docs/COMPACTION.md).

The adversarial cases: forged or partial settlement certificates, a Byzantine
rotation driver offering a checkpoint that lists live sigils or drops a
checkpointed one, a forged checkpoint set at ADOPT, a Byzantine predecessor
whose snapshot lies about a checkpointed sigil, and an owner trying to spend a
checkpointed sigil again after the rotation.
"""

import tempfile
import os
import unittest
from dataclasses import asdict

from sigil import KeyPair, Network, Wallet, locks, model
from sigil.charter import charter_body, charter_hash, checkpoint_entries, checkpoint_hash
from sigil.encoding import canonical
from sigil.network import plan_checkpoint
from sigil.store import WitnessStore
from sigil.succession import Standby
from sigil.witness import CHECKPOINTED, CONTESTED, SETTLED, Conflict, Rejected, Witness


class Base(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion", 4)
        self.owner = KeyPair.generate()
        self.exp = int(self.net.clock()) + 10 ** 9

    def parcel(self, salt, home=None):
        p = model.parcel(home or self.X, "x", 1, locks.sig(self.owner.pk), salt)
        return p, model.sigil_of(p)

    @staticmethod
    def hdr(inputs, tag):
        return {"inputs": [list(i) for i in inputs], "body": tag * 64}

    def req(self, h, sigil, p):
        u = locks.empty_unlock(self.exp)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, model.transition_id(h), self.exp)
        return {"sigil": sigil, "header": h, "home": p["home"], "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def seal(self, h, sigil, p, witnesses=None):
        ws = witnesses if witnesses is not None else self.net.witnesses(p["home"])
        return model.seal_from_votes([w.spend(self.req(h, sigil, p)) for w in ws])

    @staticmethod
    def tgt(p):
        return {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}

    def cert(self, h, parts):
        return {"header": h, "inputs": [{"parcel": self.tgt(p), "seal": seal} for p, seal in parts]}

    def next_body(self, keys, ck=None):
        cur = self.net.registry.latest(self.X)
        return charter_body(cur["name"], cur["version"] + 1, [k.pk for k in keys], charter_hash(cur), None,
                            checkpoint_hash(ck) if ck else None)


class SettleTests(Base):
    def test_a_complete_transition_settles_its_inputs(self):
        ps, s = self.parcel("s")
        Ta = self.hdr([(s, 0)], "a")
        seal = self.seal(Ta, s, ps)
        tid = model.transition_id(Ta)
        for w in self.net.witnesses(self.X):
            self.assertEqual(w.settle(self.cert(Ta, [(ps, seal)])), {"settled": [s]})
            r = w.records[s]
            self.assertEqual((r.gen, r.tid, r.settled), (0, tid, SETTLED))
            # The vote it holds for exactly this binding is handed back; nothing else is voted.
            self.assertEqual(w.spend(self.req(Ta, s, ps))["tid"], tid)
            with self.assertRaises(Conflict):
                w.spend(self.req(self.hdr([(s, 0)], "b"), s, ps))
            with self.assertRaises(Rejected):
                w.spend(self.req(self.hdr([(s, 1)], "c"), s, ps))
            with self.assertRaises(Rejected):
                w.release(s, {"kind": "seal", "sigil": s, "gen": 0, "parcel": self.tgt(ps), "seal": seal})

    def test_settle_needs_the_binding_it_settles(self):
        """SETTLE never creates or changes a binding: a witness that never saw (s, 0, Ta)
        refuses the certificate, and the sigil's record is untouched."""
        ps, s = self.parcel("s")
        Ta = self.hdr([(s, 0)], "a")
        ws = self.net.witnesses(self.X)
        seal = self.seal(Ta, s, ps, ws[:3])
        late = ws[3]
        with self.assertRaises(Rejected):
            late.settle(self.cert(Ta, [(ps, seal)]))
        self.assertNotIn(s, late.records)

    def forge(self, keys, cid, version, sigil, gen, h):
        votes = []
        for kp in keys:
            v = {"constellation": cid, "version": version, "sigil": sigil, "gen": gen,
                 "tid": model.transition_id(h), "witness": kp.pk, "time": int(self.net.clock())}
            v["sig"] = kp.sign("vote", model.vote_payload(v))
            votes.append(v)
        return model.seal_from_votes(votes)

    def test_retired_keys_cannot_rebind_a_consumed_sigil(self):
        """Review PoC1 (long-range forgery through SETTLE): s is sealed to Ta by version 0,
        the home rotates, and the retired v0 keys sign (s, 0, Tb). Before the fix every v1
        member settled at Tb, reported Tb in STATUS (deep confirmation then accepted the
        forgery and refused Ta) and the next checkpoint carried [s, 0, Tb]."""
        old = [w.kp for w in self.net.witnesses(self.X)]
        ps, s = self.parcel("s")
        Ta, Tb = self.hdr([(s, 0)], "a"), self.hdr([(s, 0)], "b")
        self.seal(Ta, s, ps)
        self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        forged = self.forge(old[:3], self.X, 0, s, 0, Tb)
        pf, f = self.parcel("fresh")                      # a sigil nobody spent yet
        Tf = self.hdr([(f, 0)], "f")
        forged_f = self.forge(old[:3], self.X, 0, f, 0, Tf)
        for w in self.net.witnesses(self.X):
            with self.assertRaises(Rejected):
                w.settle(self.cert(Tb, [(ps, forged)]))
            with self.assertRaises(Rejected):
                w.settle(self.cert(Tf, [(pf, forged_f)]))
            self.assertEqual((w.status(s)["gen"], w.status(s)["tid"]), (0, model.transition_id(Ta)))
            self.assertNotIn(f, w.records)
        self.seal(Tf, f, pf)                              # the fresh sigil is still spendable

    def test_settle_never_rewinds_a_record(self):
        """Review PoC2: an attacker-run second home seals both T (completing it) and Tk
        (killing it); s is released from T and re-spent at generation 1 as T2. A certificate
        for T must not rewind s from (1, T2) to (0, T)."""
        Y = self.net.create_constellation("mallory", 4)
        ps, s = self.parcel("s")
        py, y = self.parcel("y", Y)
        T, Tk = self.hdr([(s, 0), (y, 0)], "t"), self.hdr([(y, 0)], "k")
        seal_s, seal_yT = self.seal(T, s, ps), self.seal(T, y, py)
        cur = self.net.registry.latest(Y)["version"]
        seal_yK = self.forge([w.kp for w in self.net.witnesses(Y)[:3]], Y, cur, y, 0, Tk)
        ws = self.net.witnesses(self.X)
        for w in ws:
            w.release(s, {"kind": "seal", "sigil": y, "gen": 0, "parcel": self.tgt(py), "seal": seal_yK})
        T2 = self.hdr([(s, 1)], "2")
        self.seal(T2, s, ps)
        for w in ws:
            with self.assertRaises(Rejected):
                w.settle(self.cert(T, [(ps, seal_s), (py, seal_yT)]))
            self.assertEqual((w.status(s)["gen"], w.status(s)["tid"], w.records[s].settled),
                             (1, model.transition_id(T2), 0))

    def test_a_retired_foreign_seal_cannot_complete_a_dead_transition(self):
        """Review finding 3: T = {(a, 0) here, (y, 0) at Y}; y was really consumed by Ty, so
        T is dead and a must stay releasable (kill switch). Y rotates, and its retired keys
        forge (y, 0, T): the certificate is refused (not Y's current version), and a is
        released with Ty's seal."""
        Y = self.net.create_constellation("lyra", 4)
        pa, a = self.parcel("a")
        py, y = self.parcel("y", Y)
        T, Ty = self.hdr([(a, 0), (y, 0)], "t"), self.hdr([(y, 0)], "u")
        seal_a = self.seal(T, a, pa)
        seal_y = self.seal(Ty, y, py)
        oldY = [w.kp for w in self.net.witnesses(Y)]
        self.net.rotate(Y, [KeyPair.generate() for _ in range(4)])
        forged = self.forge(oldY[:3], Y, 0, y, 0, T)
        proof = {"kind": "seal", "sigil": y, "gen": 0, "parcel": self.tgt(py), "seal": seal_y}
        for w in self.net.witnesses(self.X):
            with self.assertRaises(Rejected):
                w.settle(self.cert(T, [(pa, seal_a), (py, forged)]))
            self.assertEqual(w.release(a, proof), 1)

    def test_one_input_sealed_is_not_a_certificate(self):
        """The kill-switch case: Tb's input s is sealed, but x was spent elsewhere, so Tb is
        dead and s must stay releasable. Only a full certificate settles."""
        ps, s = self.parcel("s")
        px, x = self.parcel("x")
        Tb, Ty = self.hdr([(s, 0), (x, 0)], "b"), self.hdr([(x, 0)], "y")
        seal_y = self.seal(Ty, x, px)
        seal_bs = self.seal(Tb, s, ps)
        w = self.net.witnesses(self.X)[0]
        bad = [
            self.cert(Tb, [(ps, seal_bs)]),                                  # one input missing
            self.cert(Tb, [(ps, seal_bs), (px, seal_y)]),                    # x's seal is for Ty
            self.cert(Tb, [(ps, seal_bs), (px, dict(seal_y, tid=model.transition_id(Tb)))]),  # forged
            self.cert(Tb, [(px, seal_bs), (ps, seal_y)]),                    # parcels swapped
            {"header": Tb}, [], "junk", {"header": Tb, "inputs": [{"parcel": 1, "seal": 2}] * 2},
        ]
        for c in bad:
            with self.assertRaises(Rejected):
                w.settle(c)
        self.assertEqual(w.records[s].settled, 0)
        proof = {"kind": "seal", "sigil": x, "gen": 0, "parcel": self.tgt(px), "seal": seal_y}
        self.assertEqual(w.release(s, proof), 1)    # still released by the kill switch

    def test_only_inputs_homed_here_are_settled(self):
        Y = self.net.create_constellation("lyra", 4)
        ps, s = self.parcel("s")
        py, y = self.parcel("y", Y)
        T = self.hdr([(s, 0), (y, 0)], "t")
        c = self.cert(T, [(ps, self.seal(T, s, ps)), (py, self.seal(T, y, py))])
        wx, wy = self.net.witnesses(self.X)[0], self.net.witnesses(Y)[0]
        self.assertEqual(wx.settle(c), {"settled": [s]})
        self.assertEqual(wy.settle(c), {"settled": [y]})
        self.assertNotIn(y, wx.records)
        Z = self.net.create_constellation("vega", 4)
        with self.assertRaises(Rejected):
            self.net.witnesses(Z)[0].settle(c)

    def test_settled_records_survive_a_restart_and_old_records_load(self):
        d = tempfile.mkdtemp()
        kp = KeyPair.generate()
        net = Network()
        X = net.create_constellation("one", 1)
        w0 = net.members[X][0]
        path = os.path.join(d, "w.db")
        w = Witness(w0.kp, net.registry, net.clock, store=WitnessStore(path))
        w.join(X, 0)
        net.members[X] = [w]
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        usd = a.issue("USD", 10)
        tid = a.pay(b, usd, 10)
        s = b.dossier.transitions[tid]["header"]["inputs"][0][0]
        self.assertEqual(w.records[s].settled, SETTLED)
        again = Witness(w0.kp, net.registry, net.clock, store=WitnessStore(path))
        self.assertEqual(asdict(again.records[s]), asdict(w.records[s]))
        # A record written before `settled` existed loads as unsettled.
        rec = asdict(w.records[s])
        del rec["settled"]
        again.store.append([("record", "old", rec)])
        self.assertEqual(Witness(w0.kp, net.registry, net.clock, store=WitnessStore(path)).records["old"].settled, 0)
        del kp


class CheckpointTests(Base):
    def settled_sigil(self, salt="s", tag="a"):
        ps, s = self.parcel(salt)
        Ta = self.hdr([(s, 0)], tag)
        seal = self.seal(Ta, s, ps)
        for w in self.net.witnesses(self.X):
            w.settle(self.cert(Ta, [(ps, seal)]))
        return ps, s, Ta, seal

    def test_rotation_checkpoints_settled_sigils_and_refuses_a_respend(self):
        ps, s, Ta, _ = self.settled_sigil()
        pl, live = self.parcel("live")
        Tl = self.hdr([(live, 0)], "l")
        for w in self.net.witnesses(self.X):
            w.spend(self.req(Tl, live, pl))   # bound, sealed, never settled
        before = sum(len(canonical(snap)) for snap in
                     [{k: list(r.log) for k, r in w.records.items()} for w in self.net.witnesses(self.X)])
        self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        body = self.net.registry.latest(self.X)
        ck = [[s, 0, model.transition_id(Ta)]]
        self.assertEqual(body["checkpoint"], checkpoint_hash(ck))
        for w in self.net.witnesses(self.X):
            r = w.records[s]
            self.assertEqual((r.gen, r.tid, r.settled, r.log, r.header), (0, model.transition_id(Ta), CHECKPOINTED, [], None))
            self.assertEqual(w.records[live].tid, model.transition_id(Tl))   # inherited as before
            self.assertEqual(w.records[live].settled, 0)
            # The owner of s signs a later generation: refused by every new member.
            with self.assertRaises(Rejected):
                w.spend(self.req(self.hdr([(s, 1)], "g"), s, ps))
            self.assertEqual(w.status(s)["tid"], model.transition_id(Ta))
        self.assertGreater(before, 0)
        # The checkpoint is carried into the next version even with nothing new settled.
        self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        self.assertEqual(self.net.registry.latest(self.X)["checkpoint"], checkpoint_hash(ck))
        self.assertEqual(self.net.witnesses(self.X)[0].records[s].settled, CHECKPOINTED)

    def test_freeze_refuses_a_checkpoint_of_live_sigils_and_changes_nothing(self):
        ps, s, Ta, _ = self.settled_sigil()
        pl, live = self.parcel("live")
        Tl = self.hdr([(live, 0)], "l")
        for w in self.net.witnesses(self.X):
            w.spend(self.req(Tl, live, pl))
        keys = [KeyPair.generate()]
        for bad in ([[live, 0, model.transition_id(Tl)]],                    # bound, not settled
                    [[s, 1, model.transition_id(Ta)]],                       # wrong generation
                    [[s, 0, "ab" * 32]]):                                    # wrong tid
            nxt = self.next_body(keys, bad)
            for w in self.net.witnesses(self.X):
                with self.assertRaises(Rejected):
                    w.freeze(nxt, bad)
                self.assertFalse(w.frozen)
        good = [[s, 0, model.transition_id(Ta)]]
        nxt = self.next_body(keys, good)
        w = self.net.witnesses(self.X)[0]
        with self.assertRaises(Rejected):          # the set does not match the charter's hash
            w.freeze(nxt, [[s, 0, model.transition_id(Tl)]])
        with self.assertRaises(Rejected):          # unsorted / malformed
            w.freeze(nxt, [[s, True, model.transition_id(Ta)]])
        self.assertFalse(w.frozen)
        sig, snap = w.freeze(nxt, good)
        self.assertNotIn(s, snap)
        self.assertIn(live, snap)

    def test_extension_rule_and_forged_sets_at_adopt(self):
        ps, s, Ta, _ = self.settled_sigil()
        self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        # A charter that drops the checkpointed sigil (an older driver, or a hostile one).
        keys = [KeyPair.generate()]
        for nxt, ck in ((self.next_body(keys), None), (self.next_body(keys, [["00" * 32, 0, "11" * 32]]), None)):
            for w in self.net.witnesses(self.X):
                with self.assertRaises(Rejected):
                    w.freeze(nxt, ck)
                self.assertFalse(w.frozen)
        # ADOPT refuses without the exact set the charter commits to.
        good = [[s, 0, model.transition_id(Ta)]]
        nxt = self.next_body(keys, good)
        sigs, snaps = {}, []
        for w in self.net.witnesses(self.X):
            sig, snap = w.freeze(nxt, good)
            sigs[w.pk], _ = sig, snaps.append(snap)
        self.net.registry.add_chain(self.X, self.net.registry.chain(self.X) + [{"body": nxt, "sigs": sigs}])
        a = Witness(keys[0], self.net.registry, self.net.clock)
        for bad in (None, [], [["00" * 32, 0, "11" * 32]], [[s, 0, "11" * 32]]):
            with self.assertRaises(Rejected):
                a.adopt(self.X, nxt["version"], snaps, bad)
            self.assertIsNone(a.cid)
        a.adopt(self.X, nxt["version"], snaps, good)
        self.assertEqual(a.records[s].settled, CHECKPOINTED)

    def test_a_lying_predecessor_cannot_reopen_a_checkpointed_sigil(self):
        """A Byzantine freezer hands over evidence for a checkpointed sigil: a bind entry at
        a later generation (the owner signs anything) and a fake 'compacted' entry. The
        adopter ignores both; the sigil stays checkpointed."""
        ps, s, Ta, _ = self.settled_sigil()
        good = [[s, 0, model.transition_id(Ta)]]
        keys = [KeyPair.generate()]
        nxt = self.next_body(keys, good)
        sigs, snaps = {}, []
        for w in self.net.witnesses(self.X)[:3]:
            sig, snap = w.freeze(nxt, good)
            sigs[w.pk] = sig
            snaps.append(snap)
        Tg = self.hdr([(s, 1)], "g")
        r = self.req(Tg, s, ps)
        auth = {k: r[k] for k in ("home", "lock", "salt", "unlock", "header")}
        lie = {s: [{"kind": "bind", "gen": 1, "auth": auth},
                   {"kind": "settled", "gen": 1, "tid": model.transition_id(Tg)}]}
        self.net.registry.add_chain(self.X, self.net.registry.chain(self.X) + [{"body": nxt, "sigs": sigs}])
        a = Witness(keys[0], self.net.registry, self.net.clock)
        a.adopt(self.X, nxt["version"], snaps + [lie], good)
        self.assertEqual((a.records[s].gen, a.records[s].tid, a.records[s].settled),
                         (0, model.transition_id(Ta), CHECKPOINTED))
        with self.assertRaises(Rejected):
            a.spend(r)

    def test_a_lying_predecessor_omitting_a_settled_sigil_is_covered_by_the_union(self):
        """A Byzantine freezer omits a sigil as if it were checkpointed, though the charter's
        checkpoint does not name it: the honest freezers' snapshots still carry the binding."""
        ps, s, Ta, _ = self.settled_sigil()
        keys = [KeyPair.generate()]
        nxt = self.next_body(keys)          # no checkpoint
        sigs, snaps = {}, []
        for w in self.net.witnesses(self.X)[:3]:
            sig, snap = w.freeze(nxt)
            sigs[w.pk] = sig
            snaps.append(snap)
        snaps[0] = {}                        # the liar hands over nothing
        self.net.registry.add_chain(self.X, self.net.registry.chain(self.X) + [{"body": nxt, "sigs": sigs}])
        a = Witness(keys[0], self.net.registry, self.net.clock)
        a.adopt(self.X, nxt["version"], snaps)
        self.assertEqual(a.records[s].tid, model.transition_id(Ta))
        with self.assertRaises(Rejected):
            a.spend(self.req(self.hdr([(s, 1)], "g"), s, ps))

    def test_plan_checkpoint(self):
        cur = {"name": "c"}
        a = {"settled": [["a", 0, "t1"], ["b", 0, "t2"]], "checkpointed": []}
        b = {"settled": [["b", 0, "t2"], ["c", 1, "t3"]], "checkpointed": []}
        self.assertEqual(plan_checkpoint(cur, [a, b]), [["b", 0, "t2"]])
        self.assertEqual(plan_checkpoint(cur, [a, b], compact=False), [])
        self.assertEqual(plan_checkpoint(cur, [a, "junk"]), [])
        prev = [["z", 0, "t9"]]
        cur = {"name": "c", "checkpoint": checkpoint_hash(prev)}
        self.assertEqual(plan_checkpoint(cur, [{"settled": [], "checkpointed": []},
                                               {"settled": [["b", 0, "t2"]], "checkpointed": prev}]),
                         prev)   # a Byzantine member's empty answer shrinks only the new part
        with self.assertRaises(RuntimeError):
            plan_checkpoint(cur, [a, b])
        self.assertEqual(checkpoint_entries({"b": (0, "t"), "a": (1, "u")}), [["a", 1, "u"], ["b", 0, "t"]])
        # A member answering with nothing (a Byzantine one, or an honest one that missed
        # the votes) limits compaction to nothing; it never blocks the rotation.
        e = [["a", 0, "t1"], ["b", 0, "t2"]]
        honest = {"settled": e, "checkpointed": []}
        self.assertEqual(plan_checkpoint({"name": "c"}, [honest, honest, {"settled": [], "checkpointed": []}, honest]), [])

    def test_a_member_that_missed_the_vote_and_a_refusing_freezer_do_not_stop_a_rotation(self):
        """Re-review PoC3: s is sealed and settled by w0..w2; w3 missed the vote, so it can
        never settle s. w0 answers SETTLED and then refuses to FREEZE. With a checkpoint chosen
        from a quorum (w0..w2), w3 refused too and the rotation failed with w1, w2 frozen for
        that charter forever. Every answering member must hold every entry."""
        ws = self.net.witnesses(self.X)
        ps, s = self.parcel("s")
        Ta = self.hdr([(s, 0)], "a")
        seal = self.seal(Ta, s, ps, ws[:3])
        for w in ws[:3]:
            w.settle(self.cert(Ta, [(ps, seal)]))
        with self.assertRaises(Rejected):
            ws[3].settle(self.cert(Ta, [(ps, seal)]))

        def refuse(*_a, **_k):
            raise Rejected("refusing to freeze")
        ws[0].freeze = refuse
        v = self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        self.assertEqual(v, 1)
        self.assertNotIn("checkpoint", self.net.registry.latest(self.X))
        for w in self.net.witnesses(self.X):
            self.assertEqual(w.status(s)["tid"], model.transition_id(Ta))

    def test_missing_settled_reply_does_not_strand_rotation(self):
        ws = self.net.witnesses(self.X)
        ps, s = self.parcel("partial")
        Ta = self.hdr([(s, 0)], "p")
        seal = self.seal(Ta, s, ps)
        for w in ws[:2]:
            w.settle(self.cert(Ta, [(ps, seal)]))

        def no_settled_reply():
            raise Rejected("SETTLED reply lost")

        for w in ws[2:]:
            w.settled_records = no_settled_reply
        self.assertEqual(self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)]), 1)
        self.assertNotIn("checkpoint", self.net.registry.latest(self.X))
        self.assertEqual({w.status(s)["tid"] for w in self.net.witnesses(self.X)},
                         {model.transition_id(Ta)})

    def test_missing_settled_reply_carries_existing_checkpoint(self):
        _, old_sigil, old_header, _ = self.settled_sigil()
        self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        inherited = [[old_sigil, 0, model.transition_id(old_header)]]
        self.assertEqual(self.net.registry.latest(self.X)["checkpoint"], checkpoint_hash(inherited))

        ws = self.net.witnesses(self.X)
        parcel, sigil = self.parcel("new")
        header = self.hdr([(sigil, 0)], "n")
        seal = self.seal(header, sigil, parcel)
        for w in ws[:2]:
            w.settle(self.cert(header, [(parcel, seal)]))

        def no_settled_reply():
            raise Rejected("SETTLED reply lost")

        for w in ws[2:]:
            w.settled_records = no_settled_reply
        self.assertEqual(self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)]), 2)
        self.assertEqual(self.net.registry.latest(self.X)["checkpoint"], checkpoint_hash(inherited))
        for w in self.net.witnesses(self.X):
            self.assertEqual(w.records[old_sigil].settled, CHECKPOINTED)
            self.assertEqual(w.status(sigil)["tid"], model.transition_id(header))
            self.assertNotEqual(w.records[sigil].settled, CHECKPOINTED)

    def test_drivers_gate_checkpoints_on_the_feature(self):
        """Review finding 4: an older daemon accepts a charter with a checkpoint but ignores the
        set (it would treat checkpointed sigils as fresh): drivers add one only if every member
        that will adopt or stand by announces the feature, and refuse to drop an existing one."""
        from sigil.server import FEATURES, _gate_checkpoint

        class M:
            def __init__(self, f):
                self.features = f
        ck = [["a", 0, "t"]]
        self.assertIn("checkpoint", FEATURES)
        self.assertEqual(_gate_checkpoint(ck, {}, [M(["checkpoint"]), M(["checkpoint"])]), ck)
        self.assertEqual(_gate_checkpoint(ck, {}, [M(["checkpoint"]), M([])]), [])
        with self.assertRaises(RuntimeError):
            _gate_checkpoint(ck, {"checkpoint": checkpoint_hash(ck)}, [M([])])


class SuccessionCheckpointTests(Base):
    def test_standby_carries_the_checkpoint_and_enforces_it(self):
        net = Network()
        X = net.create_constellation("heir", 4, successor={"n": 4, "dead_man": 100})
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        usd = a.issue("USD", 100)
        tid = a.pay(b, usd, 10)
        s = b.dossier.transitions[tid]["header"]["inputs"][0][0]
        net.rotate(X, [KeyPair.generate() for _ in range(4)], successor={"n": 4, "dead_man": 100})
        ck = [[s, 0, tid]]
        for m in net.committees[X]:
            self.assertEqual(m.checkpoint, ck)
        tid2 = b.pay(a, usd, 5)   # settled, not checkpointed
        s2 = a.dossier.transitions[tid2]["header"]["inputs"][0][0]
        cur = net.registry.latest(X)
        keys = [KeyPair.generate()]
        net.clock.advance(1000)
        m = net.committees[X][0]
        self.assertTrue(m.dead())
        # Dead man: the successor must carry exactly the version's checkpoint.
        for bad in (None, ck + [[s2, 0, tid2]] if s2 > s else [[s2, 0, tid2]] + ck):
            body = charter_body(cur["name"], cur["version"] + 1, [k.pk for k in keys], charter_hash(cur), None,
                                checkpoint_hash(bad) if bad else None)
            with self.assertRaises(Rejected):
                m.succeed(body, {}, bad)
            self.assertIsNone(m.fenced_for)
        v = net.succeed(X, [KeyPair.generate() for _ in range(4)])
        self.assertEqual(net.registry.latest(X)["checkpoint"], checkpoint_hash(ck))
        for w in net.witnesses(X):
            self.assertEqual(w.records[s].settled, CHECKPOINTED)
            self.assertEqual(w.records[s2].tid, tid2)      # from the mirror logs, as before
        self.assertEqual(v, cur["version"] + 1)
        a.pay(b, usd, 1)

    def test_standby_restart_keeps_the_checkpoint(self):
        from sigil.succession import StandbyStore
        net = Network()
        X = net.create_constellation("heir", 4, successor={"n": 1, "dead_man": 100})
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        usd = a.issue("USD", 100)
        tid = a.pay(b, usd, 10)
        s = b.dossier.transitions[tid]["header"]["inputs"][0][0]
        kp = KeyPair.generate()
        path = os.path.join(tempfile.mkdtemp(), "s.db")
        net.rotate(X, [KeyPair.generate() for _ in range(4)], successor={"keys": [kp], "dead_man": 100})
        snaps = []  # the members' snapshots are not needed: the sigil is checkpointed
        m = Standby(kp, net.registry, net.clock, store=StandbyStore(path))
        m.enter(X, 1, snaps, [[s, 0, tid]])
        again = Standby(kp, net.registry, net.clock, store=StandbyStore(path))
        self.assertEqual(again.checkpoint, [[s, 0, tid]])


class DeltaDossierTests(unittest.TestCase):
    def test_payer_omits_what_the_payee_holds_and_the_payee_still_verifies_everything(self):
        net = Network()
        X = net.create_constellation("orion", 4)
        a, b, c = Wallet("a", net, X), Wallet("b", net, X), Wallet("c", net, X, deep_threshold=1)
        usd = a.issue("USD", 1000)
        for _ in range(5):
            a.pay(b, usd, 10)
            b.pay(a, usd, 5)
        tid = a.pay(b, usd, 3)
        full = a.dossier.ancestry([tid])
        delta = a.dossier.ancestry([tid], have=b.held_history())
        self.assertLess(len(delta), len(full))
        # A payee that holds the history accepts the delta, deep confirmation included.
        tid2 = b.pay(c, usd, 4)
        self.assertEqual(c.balance(usd), 4)
        # A payee that does NOT hold the omitted history refuses it.
        tid3 = a.transact(*a.payment_outputs(usd, 2, c.address()))
        cold = a.dossier.ancestry([tid3], have=a.held_history() - {tid3})
        from sigil.validate import InvalidDossier
        d = Wallet("d", net, X)
        with self.assertRaises(InvalidDossier):
            d.receive(cold, [model.ref(tid3, 0)])
        del tid2

    def test_a_hostile_copy_of_a_held_transition_does_not_replace_ours(self):
        net = Network()
        X = net.create_constellation("orion", 4)
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        usd = a.issue("USD", 100)
        a.pay(b, usd, 10)
        b.pay(a, usd, 4)
        tid = a.transact(*a.payment_outputs(usd, 3, b.address()))
        d = a.dossier.ancestry([tid])
        for t, tx in d.transitions.items():
            if t in b.dossier.transitions and t != tid:
                d.transitions[t] = dict(tx, unlocks={})   # strip the owner's unlocks
        b.receive(d, [model.ref(tid, 0)])
        for t, tx in b.dossier.transitions.items():
            if tx["body"]["genesis"] is None:
                self.assertTrue(tx["unlocks"], "our verified copy must be kept")


if __name__ == "__main__":
    unittest.main()
