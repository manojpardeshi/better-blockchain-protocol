import unittest

from sigil import Network, Wallet
from sigil import locks, model
from sigil.wallet import SealFailed


class PledgeTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 100)
        k = self.bob.fresh_key()
        self.T = self.net.clock() + 3600
        addr = self.bob.address(lock=locks.all_of(locks.sig(k.pk), locks.after(self.T)))
        refs, outs = self.alice.payment_outputs(self.usd, 10, addr)
        tid = self.alice.transact(refs, outs)
        self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        self.held = next(h for h in self.bob.holdings.values() if h["parcel"]["lock"]["op"] == "all")
        self.sigil = self.held["sigil"]
        c = self.alice.address()
        self.out = [model.parcel(self.X, self.usd, 10, c["lock"], c["salt"])]

    def pledge(self):
        """Authorise (pledge) the time-locked spend without sealing; return its seal request."""
        h, b, _ = self.bob.prepare([self.held["ref"]], self.out)
        unlocks = self.bob.authorise(h, b)
        p = self.held["parcel"]
        return {"sigil": self.sigil, "header": h, "home": self.X, "lock": p["lock"],
                "salt": p["salt"], "unlock": unlocks[self.sigil]}

    def test_timelock_failure_drops_pledge(self):
        with self.assertRaises(SealFailed):
            self.bob.transact([self.held["ref"]], self.out)
        self.assertNotIn(self.sigil, self.bob.pledged)
        self.net.clock.advance(3600)
        self.bob.transact([self.held["ref"]], self.out)

    def test_pledge_kept_if_a_witness_voted(self):
        req = self.pledge()
        w = self.net.witnesses(self.X)[0]
        w.clock = lambda: self.T  # only this witness's clock has reached the timelock
        w.spend(req)
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        self.assertIn(self.sigil, self.bob.pledged)

    def test_pledge_kept_if_a_witness_is_down(self):
        self.pledge()
        self.net.down.add(self.net.witnesses(self.X)[0].pk)
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        self.assertIn(self.sigil, self.bob.pledged)
        self.net.down.clear()
        self.assertTrue(self.bob.unpledge_if_unbound(self.sigil))


if __name__ == "__main__":
    unittest.main()
