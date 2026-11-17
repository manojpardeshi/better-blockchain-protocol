"""Succession over the wire (SPEC §5.5, docs/WIRE.md "Succession").

Standby members served by ``StandbyServer``, witnesses by ``WitnessServer``, a
wallet on ``RemoteNetwork``: payments carry the committee's mirror acks; the
home dies; ``RemoteNetwork.succeed`` drives the takeover through ``/v0/succeed``
and ``/v0/adopt``; payments continue on the successor; the operator calls need
the admin token. bench/interop.py runs the same flows against Rust witness
processes.
"""

import unittest
from unittest.mock import patch

from sigil import Network, Wallet
from sigil.charter import Registry, charter_body, charter_hash, checkpoint_hash, successor_clause, taken_over, verify_chain
from sigil.crypto import KeyPair
from sigil.network import plan_checkpoint, settled_answers
from sigil.server import RemoteNetwork, RemoteStandby, RemoteWitness, StandbyServer, Unreachable, WitnessServer
from sigil.succession import Standby
from sigil.witness import Rejected, Witness
from tests.integration.chaos.run import ChaosRun, Config

TOKEN = "t0ken"
DEAD = 3600


class SuccessionOverHttp(unittest.TestCase):
    def setUp(self):
        self.sim = Network()
        self.ckeys = [KeyPair.generate() for _ in range(4)]
        self.X = self.sim.create_constellation("orion", successor={"keys": self.ckeys, "dead_man": DEAD})
        self.servers = []
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        self.old = self.sim.all_witnesses(self.X)
        for w in self.old:  # separate processes have separate registries
            w.registry = self._registry()
            self.servers.append(WitnessServer(w, admin_token=TOKEN).start())
        self.member_urls = [s.url for s in self.servers]
        self.committee_urls = []
        for m in self.sim.committees[self.X]:
            m.registry = self._registry()
            s = StandbyServer(m, admin_token=TOKEN).start()
            self.servers.append(s)
            self.committee_urls.append(s.url)
        self.net = RemoteNetwork({self.X: self.member_urls}, committees={self.X: self.committee_urls})

    def _registry(self):
        reg = Registry()
        reg.add_chain(self.X, self.sim.registry.chain(self.X))
        return reg

    def new_members(self, keys) -> list:
        urls = []
        for kp in keys:
            s = WitnessServer(Witness(kp, self._registry(), self.sim.clock), admin_token=TOKEN).start()
            self.servers.append(s)
            urls.append(s.url)
        return urls

    def new_standbys(self, keys) -> list:
        urls = []
        for kp in keys:
            s = StandbyServer(Standby(kp, self._registry(), self.sim.clock), admin_token=TOKEN).start()
            self.servers.append(s)
            urls.append(s.url)
        return urls

    def test_payments_carry_acks_and_a_takeover_keeps_them(self):
        alice, bob = Wallet("alice", self.net, self.X), Wallet("bob", self.net, self.X)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 40)
        self.assertTrue(all(m.mirrored for m in self.sim.committees[self.X]), "every standby member stored it")
        # The home goes silent; the committee probes over HTTP and finds nobody.
        for s in self.servers[:4]:
            s.stop()
        self.servers = self.servers[4:]
        self.sim.clock.advance(DEAD + 1)
        self.assertEqual(self.net.probe(self.X, TOKEN), 0)
        new_urls = self.new_members([KeyPair.generate() for _ in range(4)])
        new_committee = self.new_standbys([KeyPair.generate() for _ in range(4)])
        self.assertEqual(self.net.succeed(self.X, new_urls, TOKEN, committee_urls=new_committee,
                                          dead_man=DEAD), 1)
        chain = self.net.registry.chain(self.X)
        self.assertTrue(verify_chain(self.X, chain) and taken_over(chain, 0))
        self.assertEqual([w.version for w in self.net.witnesses(self.X)], [1] * 4)
        self.assertEqual({RemoteStandby(u).version for u in new_committee}, {1})
        bob.pay(alice, usd, 15)                      # acks from the new committee, votes from v1
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (75, 25))
        carol = Wallet("carol", RemoteNetwork({self.X: new_urls}, committees={self.X: new_committee}), self.X)
        alice.pay(carol, usd, 5)                     # history sealed by v0: deep-confirmed by v1
        self.assertEqual(carol.balance(usd), 5)
        self.assertGreaterEqual(len(carol._confirmed), 2)

    def test_live_home_is_not_taken_over_and_operator_calls_need_the_token(self):
        self.sim.clock.advance(DEAD + 1)
        self.assertEqual(self.net.probe(self.X, TOKEN), 16)   # 4 standby members x 4 members
        with self.assertRaises(RuntimeError):
            self.net.succeed(self.X, self.new_members([KeyPair.generate() for _ in range(4)]), TOKEN)
        cur = self.sim.registry.latest(self.X)
        nxt = charter_body("orion", 1, [KeyPair.generate().pk], charter_hash(cur))
        for token in (None, "nope"):
            with self.assertRaises(Rejected):
                RemoteStandby(self.committee_urls[0], admin_token=token).succeed(nxt)
            with self.assertRaises(Rejected):
                RemoteStandby(self.committee_urls[0], admin_token=token).probe(self.member_urls)
        # MIRROR needs no token, but only owner-authorised bindings for this version.
        with self.assertRaises(Rejected):
            RemoteStandby(self.committee_urls[0]).mirror_bind({"sigil": "x", "home": self.X, "version": 0})

    def test_network_probe_reports_standby_refusal(self):
        # A Rust standby rejects public HTTPS member URLs. The operator must see
        # that configuration error, not a count of zero live witnesses.
        with patch.object(RemoteStandby, "probe", side_effect=Rejected("only http:// URLs")):
            with self.assertRaisesRegex(Rejected, "only http:// URLs"):
                self.net.probe(self.X, TOKEN)
        # A partial count is just as misleading if one standby did not answer.
        with patch.object(RemoteStandby, "probe", side_effect=Unreachable("probe timed out")):
            with self.assertRaisesRegex(Unreachable, "probe timed out"):
                self.net.probe(self.X, TOKEN)

    def test_cooperative_rotation_over_http(self):
        alice, bob = Wallet("alice", self.net, self.X), Wallet("bob", self.net, self.X)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 40)
        urls = self.new_members([KeyPair.generate() for _ in range(4)])
        self.assertEqual(self.net.rotate(self.X, urls, TOKEN), 1)  # the committee co-signs
        chain = self.net.registry.chain(self.X)
        self.assertFalse(taken_over(chain, 0))
        self.assertNotIn("successor", chain[1]["body"])
        bob.pay(alice, usd, 10)
        self.assertEqual(self.net.committee(self.X), [])

    def test_fenced_succession_recovery_preserves_the_signed_charter(self):
        """A fenced standby must see the same charter when the live home recovers it."""
        alice, bob = Wallet("alice", self.net, self.X), Wallet("bob", self.net, self.X)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 40)
        cur = self.sim.registry.latest(self.X)
        olds = [RemoteWitness(u, admin_token=TOKEN) for u in self.member_urls]
        compacted = plan_checkpoint(cur, settled_answers(olds))
        self.assertTrue(compacted)
        self.assertEqual(plan_checkpoint(cur, settled_answers(olds), compact=False), [])
        self.assertEqual(plan_checkpoint(cur, settled_answers(self.sim.committees[self.X]), compact=False), [])

        keys = [KeyPair.generate() for _ in range(4)]
        new_urls = self.new_members(keys)
        committee_keys = [KeyPair.generate() for _ in range(4)]
        committee_urls = self.new_standbys(committee_keys)
        nxt = charter_body(cur["name"], 1, [k.pk for k in keys], charter_hash(cur),
                           successor_clause([k.pk for k in committee_keys], DEAD))
        compacted_body = charter_body(cur["name"], 1, [k.pk for k in keys], charter_hash(cur),
                                      successor_clause([k.pk for k in committee_keys], DEAD),
                                      checkpoint_hash(compacted))
        self.assertNotEqual(charter_hash(compacted_body), charter_hash(nxt))
        # A dead-man attempt signed only once before the old home was found alive.
        fenced = self.sim.committees[self.X][0]
        fenced.dead = lambda: True
        RemoteStandby(self.committee_urls[0], admin_token=TOKEN).succeed(nxt)
        self.assertEqual(fenced.fenced_for, charter_hash(nxt))

        run = ChaosRun.__new__(ChaosRun)
        run.cfg = Config(seed=1, dead_man=DEAD)
        with patch("tests.integration.chaos.run.TOKEN", TOKEN):
            self.assertEqual(run._recover_fenced_succession(self.net, self.X, new_urls, committee_urls), 1)
        chain = self.net.registry.chain(self.X)
        self.assertEqual(chain[-1]["body"], nxt)
        self.assertTrue(verify_chain(self.X, chain))
        self.assertTrue(all(m.fenced_for == charter_hash(nxt) for m in self.sim.committees[self.X]))
        bob.pay(alice, usd, 1)


if __name__ == "__main__":
    unittest.main()
