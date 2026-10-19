"""Deep confirmation (SPEC §9): checking history against the current witnesses."""

import unittest

from sigil import InvalidDossier, KeyPair, Network, Wallet
from sigil import model
from tests.test_security import manual_spend


class DeepConfirmationTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 1_000)

    def rotate_all(self):
        """Replace every witness of X with fresh keys; return the retired witnesses."""
        old = self.net.witnesses(self.X)
        self.net.rotate(self.X, [KeyPair.generate() for _ in range(4)])
        return old

    def test_honest_history_confirms(self):
        self.alice.pay(self.bob, self.usd, 300)
        carol = Wallet("carol", self.net, self.X)
        tid = self.bob.pay(carol, self.usd, 100)
        carol.deep_confirm(self.bob.dossier, [tid])

    def test_honest_history_confirms_after_rotation_and_a_crash(self):
        tid = self.alice.pay(self.bob, self.usd, 300)
        self.rotate_all()
        self.net.down.add(self.net.witnesses(self.X)[0].pk)  # f = 1 current witness unreachable
        Wallet("dave", self.net, self.X).deep_confirm(self.alice.dossier, [tid])

    def forge_with_retired_keys(self, old):
        """Alice re-spends her already-spent genesis parcel, sealed by the retired charter."""
        carol = Wallet("carol", self.net, self.X)
        a = carol.address()
        header, body, unlocks, reqs = manual_spend(
            self.alice, [model.ref(self.usd, 0)], [model.parcel(self.X, self.usd, 1_000, a["lock"], a["salt"])],
            memo="forged")
        tid = model.transition_id(header)
        s = reqs[0]["sigil"]
        seal = model.seal_from_votes([w._vote(s, 0, tid) for w in old])  # retired keys still sign
        self.alice.dossier.add_seal(seal)
        self.alice.dossier.add_transition(header, body, unlocks)
        return carol, tid

    def test_long_range_forgery_needs_deep_confirmation(self):
        self.alice.pay(self.bob, self.usd, 1_000)          # the real spend, sealed by charter v0
        old = self.rotate_all()
        carol, tid = self.forge_with_retired_keys(old)
        dossier = self.alice.dossier.ancestry([tid])
        # The forged seal is a valid v0 seal, so plain validation accepts it...
        carol.receive(dossier, [model.ref(tid, 0)], deep=False)
        # ...but the current witnesses all hold the real binding.
        dave = Wallet("dave", self.net, self.X)
        dave.keys.update(carol.keys)
        with self.assertRaises(InvalidDossier):
            dave.receive(dossier, [model.ref(tid, 0)], deep=True)

    def test_a_lying_current_minority_cannot_confirm_a_forgery(self):
        self.alice.pay(self.bob, self.usd, 1_000)
        old = self.rotate_all()
        carol, tid = self.forge_with_retired_keys(old)
        liar = self.net.witnesses(self.X)[0]               # f = 1 current witness lies for the forger
        liar.status = lambda s: {"gen": 0, "tid": tid, "votes": []}
        with self.assertRaises(InvalidDossier):
            carol.deep_confirm(self.alice.dossier, [tid])

    def test_threshold_selects_which_receipts_are_deep_confirmed(self):
        carol = Wallet("carol", self.net, self.X, deep_threshold=500)
        self.alice.pay(carol, self.usd, 10)
        self.assertEqual(carol._confirmed, set())
        self.alice.pay(carol, self.usd, 600)
        self.assertTrue(carol._confirmed)


if __name__ == "__main__":
    unittest.main()
