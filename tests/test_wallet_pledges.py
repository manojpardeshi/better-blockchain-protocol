import json
import os
import tempfile
import unittest

from sigil import InvalidDossier, Network, Wallet
from sigil import locks, model, wallet_store
from sigil.validate import Dossier
from sigil.wallet import SealFailed
from sigil.witness import Rejected


class PledgeTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 100)
        k = self.bob.fresh_key()
        # The timelock opens before an authorisation signed now expires.
        self.T = self.net.clock() + 300
        self.assertLess(300, self.bob.pledge_ttl)
        addr = self.bob.address(lock=locks.all_of(locks.sig(k.pk), locks.after(self.T)))
        refs, outs = self.alice.payment_outputs(self.usd, 10, addr)
        tid = self.alice.transact(refs, outs)
        self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        self.held = next(h for h in self.bob.holdings.values() if h["parcel"]["lock"]["op"] == "all")
        self.sigil = self.held["sigil"]
        self.out = self.outputs()

    def outputs(self):
        c = self.alice.address()
        return [model.parcel(self.X, self.usd, 10, c["lock"], c["salt"])]

    def pledge(self, out=None):
        """Authorise (pledge) the time-locked spend without sealing; return its seal request."""
        h, b, _ = self.bob.prepare([self.held["ref"]], out or self.out)
        unlocks = self.bob.authorise(h, b)
        p = self.held["parcel"]
        req = {"sigil": self.sigil, "header": h, "home": self.X, "lock": p["lock"],
               "salt": p["salt"], "unlock": unlocks[self.sigil]}
        return req, h, b, unlocks

    def expires(self):
        return self.bob.pledged[self.sigil][2]

    def advance_to(self, t):
        self.net.clock.advance(t - self.net.clock())

    def past_release(self):
        """Advance our (shared) clock past the pledge's expiry plus the skew margin."""
        self.advance_to(self.expires() + self.bob.max_skew + 1)

    # ----------------------------------------------------------- basics

    def test_pledge_records_expiry(self):
        req, h, _b, _u = self.pledge()
        gen, tid, exp = self.bob.pledged[self.sigil]
        self.assertEqual((gen, tid), (0, model.transition_id(h)))
        self.assertEqual(exp, self.net.clock() + self.bob.pledge_ttl)
        self.assertEqual(req["unlock"]["expires"], exp)

    def test_timelock_failure_keeps_pledge_until_expiry(self):
        with self.assertRaises(SealFailed):
            self.bob.transact([self.held["ref"]], self.out)
        # No witness bound it, but a delayed request still could: keep the pledge.
        self.assertIn(self.sigil, self.bob.pledged)
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        with self.assertRaises(ValueError):
            self.pledge(self.outputs())  # a different spend would be equivocation
        self.net.clock.advance(3600)
        self.bob.transact([self.held["ref"]], self.out)

    def test_reauthorising_the_same_transition_refreshes_expiry(self):
        _req, h, b, _u = self.pledge()
        first = self.expires()
        self.net.clock.advance(100)
        self.bob.authorise(h, b)
        self.assertEqual(self.expires(), first + 100)

    def test_pledge_kept_if_a_witness_voted(self):
        req, *_ = self.pledge()
        w = self.net.witnesses(self.X)[0]
        w.clock = lambda: self.T  # only this witness's clock has reached the timelock
        w.spend(req)
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        self.assertIn(self.sigil, self.bob.pledged)
        self.past_release()  # expiry does not erase a binding that exists
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        self.assertIn(self.sigil, self.bob.pledged)

    def test_pledge_kept_if_a_witness_is_down(self):
        self.pledge()
        self.past_release()
        self.net.down.add(self.net.witnesses(self.X)[0].pk)
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        self.assertIn(self.sigil, self.bob.pledged)
        self.net.down.clear()
        self.assertTrue(self.bob.unpledge_if_unbound(self.sigil))

    def test_select_releases_expired_pledges(self):
        # A plain sig-locked parcel, spent while every witness is unreachable.
        self.alice.pay(self.bob, self.usd, 5)
        self.net.down.update(w.pk for w in self.net.witnesses(self.X))
        with self.assertRaises(SealFailed):
            self.bob.pay(self.alice, self.usd, 5)
        self.net.down.clear()
        with self.assertRaises(ValueError):
            self.bob.select(self.usd, 5)  # still pledged: not yet expired
        self.net.clock.advance(self.bob.pledge_ttl + self.bob.max_skew + 1)
        self.bob.pay(self.alice, self.usd, 5)  # select released the expired pledge

    # ------------------------------------------------- delayed requests

    def test_delayed_request_after_expiry_cannot_bind(self):
        """The race expiry closes: a failed spend's request reaches a witness late."""
        req, h, b, unlocks = self.pledge()
        with self.assertRaises(SealFailed):
            self.bob.seal(h, b, unlocks)  # the timelock is not yet open anywhere
        # Every witness answers and none is bound, yet the original request may
        # still be in flight: releasing now could lead the owner to equivocate.
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        self.assertIn(self.sigil, self.bob.pledged)
        # The delayed request arrives after the authorisation expired (and the
        # timelock opened): it is refused and binds nothing.
        self.advance_to(self.expires() + 1)
        for w in self.net.witnesses(self.X):
            with self.assertRaises(Rejected) as ctx:
                w.spend(req)
            self.assertIn("authorisation expired", str(ctx.exception))
            self.assertIsNone(w.status(self.sigil)["tid"])
            self.assertEqual(w.status(self.sigil)["votes"], [])
        # Within the skew margin the wallet still waits...
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))
        # ...and afterwards releases, so a different spend of the sigil can seal.
        self.past_release()
        self.assertTrue(self.bob.unpledge_if_unbound(self.sigil))
        tid = self.bob.transact([self.held["ref"]], self.outputs())
        self.assertNotEqual(tid, model.transition_id(h))
        for w in self.net.witnesses(self.X):
            self.assertEqual(w.status(self.sigil)["tid"], tid)

    def test_delayed_request_before_expiry_binds_and_pledge_is_kept(self):
        req, h, b, unlocks = self.pledge()
        with self.assertRaises(SealFailed):
            self.bob.seal(h, b, unlocks)
        self.advance_to(self.T)  # timelock open, authorisation not yet expired
        self.assertLessEqual(self.net.clock(), self.expires())
        w = self.net.witnesses(self.X)[0]
        w.spend(req)  # the delayed request binds this witness
        self.assertEqual(w.status(self.sigil)["tid"], model.transition_id(h))
        self.past_release()
        self.assertFalse(self.bob.unpledge_if_unbound(self.sigil))  # correctly kept
        self.assertIn(self.sigil, self.bob.pledged)
        with self.assertRaises(ValueError):
            self.pledge(self.outputs())  # never sign a conflicting spend
        # The owner can still finish the *same* spend with a fresh authorisation.
        unlocks = self.bob.authorise(h, b)
        self.assertGreater(unlocks[self.sigil]["expires"], req["unlock"]["expires"])
        self.bob.seal(h, b, unlocks)
        self.bob.finalise(h, b, unlocks)
        self.assertNotIn(self.held["ref"], [x["ref"] for x in self.bob.holdings.values()])

    def test_existing_binding_revotes_after_expiry(self):
        req, *_ = self.pledge()
        self.advance_to(self.T)
        w = self.net.witnesses(self.X)[0]
        vote = w.spend(req)
        self.past_release()
        self.assertEqual(w.spend(req), vote)  # re-voting an existing binding is allowed
        other = self.net.witnesses(self.X)[1]
        with self.assertRaises(Rejected):
            other.spend(req)  # but nobody newly binds on it

    # ---------------------------------------------------- holder checks

    def test_holder_rejects_tampered_expiry(self):
        tid = self.alice.pay(self.bob, self.usd, 7)
        d = Dossier.from_json(self.alice.dossier.ancestry([tid]).to_json())
        tx = d.transitions[tid]
        s, _g = tx["header"]["inputs"][0]
        p = d.output(tx["body"]["inputs"][0])
        self.assertTrue(locks.evaluate(p["lock"], tx["unlocks"][s], s, tid, None))
        tx["unlocks"][s]["expires"] += 1  # the signature covers the expiry
        self.assertFalse(locks.evaluate(p["lock"], tx["unlocks"][s], s, tid, None))
        carol = Wallet("carol", self.net, self.X)
        with self.assertRaises(InvalidDossier):
            carol.verifier.verify_transition(d, tid)

    # ---------------------------------------------------- persistence

    def test_legacy_two_item_pledges_load(self):
        self.pledge()
        path = tempfile.mkdtemp()
        wallet_store.save(self.bob, path)
        with open(os.path.join(path, "state.json")) as f:
            state = json.load(f)
        self.assertEqual(len(state["pledged"][self.sigil]), 3)
        state["pledged"][self.sigil] = state["pledged"][self.sigil][:2]
        with open(os.path.join(path, "state.json"), "w") as f:
            json.dump(state, f)
        loaded = wallet_store.load(path, self.net)
        gen, tid, exp = loaded.pledged[self.sigil]
        self.assertEqual((gen, tid, exp), (*self.bob.pledged[self.sigil][:2], 0))


if __name__ == "__main__":
    unittest.main()
