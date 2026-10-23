import json
import unittest

from sigil import InvalidDossier, Network, SealFailed, Wallet
from sigil import locks, model
from sigil.encoding import hash_preimage
from sigil.proofs import verify_equivocation, verify_seal
from sigil.wallet import request_seal
from sigil.witness import Conflict, Rejected
from tests.adversary import Equivocator, Silent


def manual_spend(wallet, refs, outputs, memo=""):
    """Build and sign a transition *without* the wallet's anti-equivocation guard."""
    header, body, tid = wallet.prepare(refs, outputs, memo)
    expires = wallet.clock() + wallet.pledge_ttl
    unlocks = {}
    for r, (s, _) in zip(refs, header["inputs"]):
        p = wallet.dossier.output(r)
        u = locks.empty_unlock(expires)
        for pk in locks.keys_in(p["lock"]) & set(wallet.keys):
            u["sigs"][pk] = locks.sign_unlock(wallet.keys[pk], s, tid, expires)
        unlocks[s] = u
    reqs = []
    for r, (s, _) in zip(refs, header["inputs"]):
        p = wallet.dossier.output(r)
        reqs.append({"sigil": s, "header": header, "home": p["home"], "lock": p["lock"],
                     "salt": p["salt"], "unlock": unlocks[s]})
    return header, body, unlocks, reqs


class DoubleSpendTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion", byzantine={3: Equivocator})
        self.mallory = Wallet("mallory", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.carol = Wallet("carol", self.net, self.X)
        self.usd = self.mallory.issue("USD", 100)

    def _two_spends(self):
        refs, _ = self.mallory.select(self.usd, 100)
        to_bob, to_carol = self.bob.address(), self.carol.address()
        t1 = manual_spend(self.mallory, refs, [model.parcel(self.X, self.usd, 100, to_bob["lock"], to_bob["salt"])])
        t2 = manual_spend(self.mallory, refs, [model.parcel(self.X, self.usd, 100, to_carol["lock"], to_carol["salt"])])
        return t1, t2

    def test_wallet_refuses_to_equivocate(self):
        refs, _ = self.mallory.select(self.usd, 100)
        a, b = self.bob.address(), self.carol.address()
        h1, b1, _ = self.mallory.prepare(refs, [model.parcel(self.X, self.usd, 100, a["lock"], a["salt"])])
        h2, b2, _ = self.mallory.prepare(refs, [model.parcel(self.X, self.usd, 100, b["lock"], b["salt"])])
        self.mallory.authorise(h1, b1)
        with self.assertRaises(ValueError):
            self.mallory.authorise(h2, b2)

    def test_sequential_double_spend_fails(self):
        (h1, b1, u1, r1), (h2, b2, u2, r2) = self._two_spends()
        request_seal(self.net, r1[0])
        with self.assertRaises(SealFailed) as ctx:
            request_seal(self.net, r2[0])
        self.assertEqual(len(ctx.exception.conflicts), 3)  # every honest witness objects

    def test_split_double_spend_with_byzantine_witness(self):
        """Mallory sends each spend to a different half and recruits the byzantine witness."""
        (h1, *_ , r1), (h2, *_, r2) = self._two_spends()
        honest = self.net.witnesses(self.X)[:3]
        byz = self.net.witnesses(self.X)[3]
        v1 = [honest[0].spend(r1[0]), honest[1].spend(r1[0]), byz.spend(r1[0])]
        v2 = [byz.spend(r2[0])]
        with self.assertRaises(Conflict):
            honest[0].spend(r2[0])
        v2.append(honest[2].spend(r2[0]))
        seal1 = model.seal_from_votes(v1)
        seal2 = model.seal_from_votes(v2)
        self.assertTrue(verify_seal(seal1, self.net.registry))
        self.assertFalse(verify_seal(seal2, self.net.registry))  # 2 < quorum of 3
        # ...and the byzantine witness has signed its own conviction.
        proof = {"a": v1[2], "b": v2[0]}
        self.assertTrue(verify_equivocation(proof))
        self.assertTrue(self.bob.policy.convict(proof))
        # Convicted votes stop counting, so seal1 now needs a third honest vote.
        self.assertFalse(verify_seal(seal1, self.net.registry, self.bob.policy.convicted))

    def test_equivocation_slashes_a_bond(self):
        """A witness's bond is a parcel anyone can claim with proof of equivocation."""
        byz = self.net.witnesses(self.X)[3]
        operator = Wallet("operator", self.net, self.X)
        stake = operator.issue("STAKE", 1_000)
        T = self.net.clock() + 365 * 86400
        op_key = operator.fresh_key()
        bond_lock = locks.any_of(locks.all_of(locks.sig(op_key.pk), locks.after(T)),
                                 locks.equivocation(byz.pk))
        refs, _ = operator.select(stake, 1_000)
        bond_tid = operator.transact(refs, [model.parcel(self.X, stake, 1_000, bond_lock, "bond")])
        # Byzantine witness equivocates.
        (h1, *_, r1), (h2, *_, r2) = self._two_spends()
        proof = {"a": byz.spend(r1[0]), "b": byz.spend(r2[0])}
        # A bounty hunter claims the bond, years before the operator could unbond.
        hunter = Wallet("hunter", self.net, self.X)
        hunter.watch(operator.dossier.ancestry([bond_tid]), model.ref(bond_tid, 0))
        bond = next(h for h in hunter.holdings.values() if h["parcel"]["asset"] == stake)
        a = hunter.address()
        hunter.transact([bond["ref"]], [model.parcel(self.X, stake, 1_000, a["lock"], a["salt"])],
                                extra_unlocks={bond["sigil"]: {"equivocations": [proof]}})
        self.assertEqual(hunter.balance(stake), 1_000)


class TheftTests(unittest.TestCase):
    def test_fully_corrupt_quorum_cannot_steal(self):
        net = Network()
        evil = net.create_constellation("evil", byzantine={i: Equivocator for i in range(4)})
        alice, eve, carol = (Wallet(n, net, evil) for n in ("alice", "eve", "carol"))
        usd = alice.issue("USD", 100)
        refs, _ = alice.select(usd, 100)
        eve.dossier.merge(alice.dossier)
        a = carol.address()
        header, body, tid = eve.prepare(refs, [model.parcel(evil, usd, 100, a["lock"], a["salt"])])
        p = eve.dossier.output(refs[0])
        s = model.sigil_of(p)
        req = {"sigil": s, "header": header, "home": evil, "lock": p["lock"], "salt": p["salt"],
               "unlock": locks.empty_unlock(net.clock() + 600)}
        eve.dossier.add_seal(request_seal(net, req))  # the corrupt witnesses happily seal it
        eve.dossier.add_transition(header, body, {})
        with self.assertRaises(InvalidDossier) as ctx:
            carol.receive(eve.dossier.ancestry([tid]), [model.ref(tid, 0)])
        self.assertIn("authorise", str(ctx.exception))


class WitnessTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 777_777)

    def test_witnesses_are_blind_to_value(self):
        self.alice.pay(self.bob, self.usd, 123_456)
        for w in self.net.witnesses(self.X):
            state = json.dumps({s: r.log for s, r in w.records.items()})
            for secret in (self.usd, "123456", "777777", '"amount"', '"asset"'):
                self.assertNotIn(secret, state)

    def test_timelock_is_attested_by_witness_clocks(self):
        k = self.bob.fresh_key()
        T = self.net.clock() + 3600
        addr = self.bob.address(lock=locks.all_of(locks.sig(k.pk), locks.after(T)))
        refs, outs = self.alice.payment_outputs(self.usd, 10, addr)
        tid = self.alice.transact(refs, outs)
        self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        held = next(h for h in self.bob.holdings.values() if h["parcel"]["lock"]["op"] == "all")
        c = self.alice.address()
        out = [model.parcel(self.X, self.usd, 10, c["lock"], c["salt"])]
        with self.assertRaises(SealFailed):
            self.bob.transact([held["ref"]], out)
        self.net.clock.advance(3600)
        self.bob.transact([held["ref"]], out)

    def test_hashlock(self):
        pre = "00" * 31 + "2a"
        addr = self.bob.address(lock=locks.all_of(locks.sig(self.bob.fresh_key().pk), locks.hashlock(hash_preimage(pre))))
        refs, outs = self.alice.payment_outputs(self.usd, 10, addr)
        tid = self.alice.transact(refs, outs)
        self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        held = next(h for h in self.bob.holdings.values() if h["parcel"]["lock"]["op"] == "all")
        c = self.alice.address()
        self.bob.transact([held["ref"]], [model.parcel(self.X, self.usd, 10, c["lock"], c["salt"])],
                          extra_unlocks={held["sigil"]: {"preimages": {hash_preimage(pre): pre}}})

    def test_wrong_signer_is_rejected(self):
        refs, _ = self.alice.select(self.usd, 1)
        h, b, tid = self.alice.prepare(refs, [])
        p = self.alice.dossier.output(refs[0])
        s = model.sigil_of(p)
        exp = self.net.clock() + 600
        u = locks.empty_unlock(exp)
        u["sigs"][p["lock"]["pk"]] = locks.sign_unlock(self.bob.fresh_key(), s, tid, exp)
        req = {"sigil": s, "header": h, "home": self.X, "lock": p["lock"], "salt": p["salt"], "unlock": u}
        for w in self.net.witnesses(self.X):
            with self.assertRaises(Rejected):
                w.spend(req)

    def test_tolerates_f_crashes_but_not_more(self):
        ws = self.net.witnesses(self.X)
        self.net.down.add(ws[0].pk)
        self.alice.pay(self.bob, self.usd, 1)
        self.net.down.add(ws[1].pk)
        with self.assertRaises(SealFailed):
            self.alice.pay(self.bob, self.usd, 1)

    def test_censoring_minority_cannot_block(self):
        net = Network()
        X = net.create_constellation("orion", byzantine={0: Silent})
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        coin = a.issue("C", 5)
        a.pay(b, coin, 5)
        self.assertEqual(b.balance(coin), 5)

    def test_stamps_pay_for_attention(self):
        net = Network()
        X = net.create_constellation("paid", stamps=True)
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        coin = a.issue("C", 5)
        with self.assertRaises(SealFailed):
            a.pay(b, coin, 1)
        # The failed spend's pledge holds the coin until its authorisation expires.
        net.clock.advance(a.pledge_ttl + a.max_skew + 1)
        a.buy_stamps(X, 1)
        a.pay(b, coin, 1)
        # A stamp is single use.
        w = net.witnesses(X)[0]
        st = {"serial": "ab" * 16, "sig": "1"}
        self.assertFalse(w.stamps.redeem(st))


if __name__ == "__main__":
    unittest.main()
