"""Wallets talking to witnesses over real HTTP (wire protocol v0)."""

import json
import tempfile
import unittest
import urllib.request

from sigil import InvalidDossier, KeyPair, Network, SealFailed, Wallet
from sigil import model
from sigil.charter import charter_body, constellation_id
from sigil.server import RemoteNetwork, RemoteWitness, WitnessServer
from sigil.store import WitnessStore
from sigil.swap import atomic_swap
from sigil.witness import Conflict, Rejected, Witness
from tests.test_security import manual_spend


class WireTests(unittest.TestCase):
    def setUp(self):
        # Witness processes are built in-process, then reached only over HTTP.
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.Y = self.sim.create_constellation("lyra", stamps=True)
        self.servers = {cid: [WitnessServer(w).start() for w in self.sim.all_witnesses(cid)]
                        for cid in (self.X, self.Y)}
        self.addCleanup(lambda: [s.stop() for ss in self.servers.values() for s in ss])
        self.net = RemoteNetwork({cid: [s.url for s in ss] for cid, ss in self.servers.items()})

    def test_durable_witness_serves_over_http(self):
        """Regression: a store opened on one thread must serve the handler threads."""
        sim = Network()
        kp = KeyPair.generate()
        body = charter_body("durable", 0, [kp.pk], None)
        cid = constellation_id(body)
        sim.registry.add_chain(cid, [{"body": body, "sigs": {}}])
        w = Witness(kp, sim.registry, sim.clock, store=WitnessStore(f"{tempfile.mkdtemp()}/w.db"))
        w.join(cid, 0)
        srv = WitnessServer(w).start()
        self.addCleanup(srv.stop)
        net = RemoteNetwork({cid: [srv.url]})
        alice, bob = Wallet("alice", net, cid), Wallet("bob", net, cid)
        coin = alice.issue("C", 5)
        alice.pay(bob, coin, 2)
        self.assertEqual(bob.balance(coin), 2)

    def test_charters_are_fetched_and_verified(self):
        self.assertEqual(self.net.registry.chain(self.X), self.sim.registry.chain(self.X))
        self.assertEqual(len(self.net.witnesses(self.X)), 4)

    def test_payments_swaps_and_deep_confirmation_over_http(self):
        alice, bob = Wallet("alice", self.net, self.X), Wallet("bob", self.net, self.X)
        usd = alice.issue("USD", 1_000)
        tid = alice.pay(bob, usd, 300)
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (700, 300))
        Wallet("carol", self.net, self.X).deep_confirm(alice.dossier, [tid])
        gold = bob.issue("GOLD", 10)
        atomic_swap(alice, usd, 100, bob, gold, 2)
        self.assertEqual((alice.balance(gold), bob.balance(usd)), (2, 400))

    def test_stamps_over_http(self):
        clock = self.sim.clock  # the witnesses' clock
        alice, bob = Wallet("alice", self.net, self.Y, clock=clock), Wallet("bob", self.net, self.Y)
        coin = alice.issue("C", 5)
        with self.assertRaises(SealFailed):
            alice.pay(bob, coin, 1)
        # The failed spend's pledge holds the coin until its authorisation expires.
        clock.advance(alice.pledge_ttl + alice.max_skew + 1)
        alice.buy_stamps(self.Y, 1)
        alice.pay(bob, coin, 1)

    def test_conflicts_cross_the_wire(self):
        alice, bob, carol = (Wallet(n, self.net, self.X) for n in ("alice", "bob", "carol"))
        usd = alice.issue("USD", 10)
        refs, _ = alice.select(usd, 10)
        b, c = bob.address(), carol.address()
        *_, r1 = manual_spend(alice, refs, [model.parcel(self.X, usd, 10, b["lock"], b["salt"])])
        *_, r2 = manual_spend(alice, refs, [model.parcel(self.X, usd, 10, c["lock"], c["salt"])])
        w = self.net.witnesses(self.X)[0]
        vote = w.spend(r1[0])
        with self.assertRaises(Conflict) as ctx:
            w.spend(r2[0])
        self.assertEqual(ctx.exception.vote, vote)

    def test_a_crashed_witness_is_tolerated(self):
        alice, bob = Wallet("alice", self.net, self.X), Wallet("bob", self.net, self.X)
        usd = alice.issue("USD", 10)
        self.servers[self.X][0].stop()                  # one of four witnesses goes away
        alice.pay(bob, usd, 3)
        self.servers[self.X][1].stop()                  # now two: no quorum
        with self.assertRaises(SealFailed):
            alice.pay(bob, usd, 3)

    def test_unreachable_witness_keeps_pledge(self):
        alice = Wallet("alice", self.net, self.X, clock=self.sim.clock)
        usd = alice.issue("USD", 10)
        refs, _ = alice.select(usd, 10)
        a = alice.address()
        header, body, _ = alice.prepare(refs, [model.parcel(self.X, usd, 10, a["lock"], a["salt"])])
        alice.authorise(header, body)
        s = header["inputs"][0][0]
        self.servers[self.X][3].stop()
        self.sim.clock.advance(alice.pledge_ttl + alice.max_skew + 1)  # expiry alone is not enough
        self.assertFalse(alice.unpledge_if_unbound(s))  # can't prove the stopped witness holds no vote
        self.assertIn(s, alice.pledged)

    def test_malformed_requests_are_rejected_not_crashing(self):
        url = self.servers[self.X][0].url
        for body in (b"[]", b"not json", json.dumps({"request": 5}).encode()):
            req = urllib.request.Request(f"{url}/v0/spend", data=body, method="POST")
            with self.assertRaises(urllib.error.HTTPError) as ctx:
                urllib.request.urlopen(req, timeout=5)
            self.assertIn(ctx.exception.code, (400, 403))
        RemoteWitness(url).status("00" * 32)  # still serving

    def test_forged_charter_from_a_witness_is_ignored(self):
        rogue = self.servers[self.X][0]
        real = rogue.witness.registry.chain
        rogue.witness.registry.chain = lambda cid: [{"body": {"name": "fake", "version": 0,
                                                              "witnesses": ["aa"], "prev": None}, "sigs": {}}]
        try:
            fresh = RemoteNetwork({self.X: [rogue.url]})
            self.assertIsNone(fresh.registry.latest(self.X))
        finally:
            rogue.witness.registry.chain = real


if __name__ == "__main__":
    unittest.main()
