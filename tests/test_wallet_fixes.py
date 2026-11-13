"""Regression tests for wallet fixes: pledge pruning, charter-member answers,
and the generation limit."""

import json
import os
import tempfile
import unittest

from sigil import InvalidDossier, KeyPair, Network, Wallet
from sigil import model, wallet_store
from sigil.witness import Witness


class PledgePruneTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 100)

    def test_finalise_drops_pledges_of_consumed_inputs(self):
        spent = [h["sigil"] for h in self.alice.holdings.values()]
        self.alice.pay(self.bob, self.usd, 10)
        for s in spent:
            self.assertIn(s, self.alice.spent)
            self.assertNotIn(s, self.alice.pledged)
        # Every pledge left belongs to something still held.
        held = {h["sigil"] for h in self.alice.holdings.values()}
        self.assertLessEqual(set(self.alice.pledged), held)

    def test_old_store_with_stale_pledges_loads_pruned(self):
        spent = [h["sigil"] for h in self.alice.holdings.values()]
        self.alice.pay(self.bob, self.usd, 10)
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        wallet_store.save(self.alice, d.name)
        path = os.path.join(d.name, "state.json")
        with open(path) as f:
            state = json.load(f)
        # A wallet saved by the old code still lists the consumed inputs' pledges.
        for s in spent:
            state["pledged"][s] = [0, "00" * 32, 0]
        with open(path, "w") as f:
            json.dump(state, f)
        loaded = wallet_store.load(d.name, self.net)
        for s in spent:
            self.assertNotIn(s, loaded.pledged)
        loaded.pay(self.bob, self.usd, 5)


class CharterMemberAnswerTests(unittest.TestCase):
    """Rule 3, receive and deep confirmation count one answer per CURRENT charter key."""

    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 100)
        self.ws = list(self.net.all_witnesses(self.X))

    def pledge_with_one_vote(self):
        """Bob authorises a spend; only witness 0 votes on it. Returns the sigil."""
        self.alice.pay(self.bob, self.usd, 10)
        h = next(iter(self.bob.holdings.values()))
        c = self.alice.address()
        hd, bd, _ = self.bob.prepare([h["ref"]], [model.parcel(self.X, self.usd, 10, c["lock"], c["salt"])])
        unlocks = self.bob.authorise(hd, bd)
        p = h["parcel"]
        self.ws[0].spend({"sigil": h["sigil"], "header": hd, "home": self.X, "lock": p["lock"],
                          "salt": p["salt"], "unlock": unlocks[h["sigil"]]})
        self.net.clock.advance(self.bob.pledge_ttl + self.bob.max_skew + 1)
        return h["sigil"]

    def test_rule3_ignores_a_member_listed_twice(self):
        s = self.pledge_with_one_vote()
        # The directory lists member 1 twice and omits member 0 (which holds the vote).
        self.net.members[self.X] = [self.ws[1], self.ws[1], self.ws[2], self.ws[3]]
        self.assertFalse(self.bob.unpledge_if_unbound(s))
        self.assertIn(s, self.bob.pledged)

    def test_rule3_ignores_a_retired_member(self):
        s = self.pledge_with_one_vote()
        # A key that is not (or no longer) in the current charter, answering "unbound".
        stale = Witness(KeyPair.generate(), self.net.registry, self.net.clock)
        self.net.members[self.X] = [stale, self.ws[1], self.ws[2], self.ws[3]]
        self.assertFalse(self.bob.unpledge_if_unbound(s))
        self.assertIn(s, self.bob.pledged)
        self.net.members[self.X] = self.ws  # the real membership: still bound at member 0
        self.assertFalse(self.bob.unpledge_if_unbound(s))

    def test_receive_needs_a_quorum_of_distinct_members(self):
        addr = self.bob.address()
        refs, outs = self.alice.payment_outputs(self.usd, 10, addr)
        tid = self.alice.transact(refs, outs)
        self.net.members[self.X] = [self.ws[1]] * 3  # three answers, one member
        with self.assertRaises(InvalidDossier):
            self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        self.net.members[self.X] = self.ws
        self.bob.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])

    def test_deep_confirm_counts_each_member_once(self):
        carol = Wallet("carol", self.net, self.X)
        tid = self.alice.pay(self.bob, self.usd, 10)
        spent = self.bob.dossier.transitions[tid]["header"]["inputs"][0][0]
        for w in self.ws[1:]:
            w.records.pop(spent, None)  # only member 0 still reports the binding
        self.net.members[self.X] = [self.ws[0], self.ws[0], self.ws[1], self.ws[2]]
        with self.assertRaises(InvalidDossier):
            carol.deep_confirm(self.bob.dossier, [tid])


if __name__ == "__main__":
    unittest.main()
