import copy
import unittest

from sigil import InvalidDossier, Network, Wallet
from sigil import locks, model
from sigil.swap import atomic_swap
from sigil.validate import Dossier


class PaymentTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.Y = self.net.create_constellation("lyra")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.Y)
        self.carol = Wallet("carol", self.net, self.X)
        self.usd = self.alice.issue("USD", 1_000)

    def test_issue_and_pay_with_change(self):
        self.alice.pay(self.bob, self.usd, 300)
        self.assertEqual(self.alice.balance(self.usd), 700)
        self.assertEqual(self.bob.balance(self.usd), 300)

    def test_payment_chain_across_constellations(self):
        self.alice.pay(self.bob, self.usd, 300)        # X -> Y
        self.bob.pay(self.carol, self.usd, 120)        # Y -> X
        self.carol.pay(self.alice, self.usd, 20, home=self.Y)
        self.assertEqual(
            [w.balance(self.usd) for w in (self.alice, self.bob, self.carol)], [720, 180, 100]
        )

    def test_many_small_payments_merge_inputs(self):
        for _ in range(5):
            self.alice.pay(self.bob, self.usd, 10)
        self.bob.pay(self.carol, self.usd, 45)  # needs 5 inputs
        self.assertEqual(self.carol.balance(self.usd), 45)
        self.assertEqual(self.bob.balance(self.usd), 5)

    def test_insufficient_funds(self):
        with self.assertRaises(ValueError):
            self.alice.pay(self.bob, self.usd, 1_001)

    def test_mint_cap_is_enforced(self):
        gold = self.alice.issue("GOLD", 10, mint_cap=5)
        self.alice.mint(gold, 3)
        self.alice.mint(gold, 2)
        self.assertEqual(self.alice.balance(gold), 15)
        with self.assertRaises(ValueError):
            self.alice.mint(gold, 1)  # mint right fully used up

    def test_atomic_swap_across_constellations(self):
        gold = self.bob.issue("GOLD", 50)
        atomic_swap(self.alice, self.usd, 100, self.bob, gold, 5)
        self.assertEqual(self.alice.balance(gold), 5)
        self.assertEqual(self.bob.balance(self.usd), 100)
        # Both can keep spending what they received.
        self.bob.pay(self.carol, self.usd, 100)
        self.alice.pay(self.carol, gold, 5)
        self.assertEqual((self.carol.balance(self.usd), self.carol.balance(gold)), (100, 5))

    def test_dossier_round_trips_through_json(self):
        tid = self.alice.pay(self.bob, self.usd, 1)
        d = Dossier.from_json(self.alice.dossier.ancestry([tid]).to_json())
        dave = Wallet("dave", self.net, self.X)
        dave.verifier.verify_parcel(d, model.ref(tid, 0))

    def test_tampered_dossier_is_rejected(self):
        tid = self.alice.pay(self.bob, self.usd, 300)
        d = self.alice.dossier.ancestry([tid])
        bad = copy.deepcopy(d)
        bad.transitions[tid]["body"]["outputs"][0]["amount"] = 900
        with self.assertRaises(InvalidDossier):
            Wallet("eve", self.net, self.X).verifier.verify_parcel(bad, model.ref(tid, 0))
        bad = copy.deepcopy(d)
        bad.seals.clear()
        with self.assertRaises(InvalidDossier):
            Wallet("eve", self.net, self.X).verifier.verify_parcel(bad, model.ref(tid, 0))

    def test_witnesses_seal_inflation_but_holders_reject_it(self):
        """Witnesses are blind: they will seal a transition that creates money.

        It does not matter. Validity is decided by whoever receives the
        parcel, and no honest holder accepts it.
        """
        refs, _ = self.alice.select(self.usd, 1_000)
        addr = self.carol.address()
        outputs = [model.parcel(addr["home"], self.usd, 5_000, addr["lock"], addr["salt"])]
        tid = self.alice.transact(refs, outputs)  # sealed fine
        with self.assertRaises(InvalidDossier):
            self.carol.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])

    def test_untrusted_constellation_is_rejected(self):
        rogue = self.net.create_constellation("rogue")
        picky = Wallet("picky", self.net, self.X, trusted={self.X})
        refs, _ = self.alice.select(self.usd, 1)
        a = picky.address(home=rogue)
        tid = self.alice.transact(refs, [model.parcel(rogue, self.usd, 1_000, a["lock"], a["salt"])])
        with self.assertRaises(InvalidDossier):
            picky.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])

    def test_recipient_can_choose_any_lock(self):
        k1, k2, k3 = (self.bob.fresh_key() for _ in range(3))
        addr = self.bob.address(lock=locks.multi(2, [k1.pk, k2.pk, k3.pk]))
        refs, outs = self.alice.payment_outputs(self.usd, 50, addr)
        tid = self.alice.transact(refs, outs)
        self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        held = next(h for h in self.bob.holdings.values() if h["parcel"]["lock"]["op"] == "multi")
        c = self.carol.address()
        self.bob.transact([held["ref"]], [model.parcel(c["home"], self.usd, 50, c["lock"], c["salt"])])


if __name__ == "__main__":
    unittest.main()
