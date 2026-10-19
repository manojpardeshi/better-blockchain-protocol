"""Gossip of charter chains and equivocation proofs over real HTTP."""

import json
import unittest
import urllib.error
import urllib.request

from sigil import InvalidDossier, Network, Wallet
from sigil import gossip as G
from sigil.charter import Registry, charter_body, charter_hash, constellation_id, sign_charter
from sigil.crypto import KeyPair
from sigil.gossip import GossipStore, equivocations_in, fork_signers, gossip_round, verify_fork
from sigil.proofs import verify_equivocation, verify_seal
from sigil.server import RemoteNetwork, RemoteWitness, Unreachable, WitnessServer
from sigil.witness import Rejected


def post(url: str, body) -> tuple[int, dict]:
    req = urllib.request.Request(f"{url}/v0/gossip", data=json.dumps(body).encode(), method="POST")
    try:
        with urllib.request.urlopen(req, timeout=5) as r:
            return r.status, json.loads(r.read())
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read())


class GossipTests(unittest.TestCase):
    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.ws = self.sim.all_witnesses(self.X)
        # Every witness gets its own registry, as separate processes would.
        for w in self.ws:
            w.registry = Registry()
            w.registry.add_chain(self.X, self.sim.registry.chain(self.X))
        self.servers = [WitnessServer(w).start() for w in self.ws]
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        self.net = RemoteNetwork({self.X: [s.url for s in self.servers]})

    # ---------------------------------------------------------- helpers

    def next_charter(self, signers, new_keys=None, name="orion") -> dict:
        cur = self.sim.registry.latest(self.X)
        pks = [k.pk for k in new_keys] if new_keys else [w.pk for w in self.ws]
        body = charter_body(name, cur["version"] + 1, pks, charter_hash(cur))
        return {"body": body, "sigs": {w.pk: sign_charter(w.kp, body) for w in signers}}

    def equivocation(self, w) -> dict:
        return {"a": w._vote("11" * 32, 0, "aa" * 32), "b": w._vote("11" * 32, 0, "bb" * 32)}

    def server_chain_len(self, s) -> int:
        return len(s.witness.registry.chain(self.X))

    # ------------------------------------------------------------ tests

    def test_rotation_known_to_one_witness_reaches_wallet_and_witnesses(self):
        v1 = self.next_charter(self.ws[:3], new_keys=[KeyPair.generate() for _ in range(4)])
        chain = self.sim.registry.chain(self.X) + [v1]
        self.servers[0].witness.registry.add_chain(self.X, chain)   # only witness 0 knows
        self.assertEqual(self.net.registry.latest(self.X)["version"], 0)

        store = GossipStore(self.net.registry)
        out = gossip_round(self.net, store)
        self.assertEqual(out["learned"]["charters"], 1)
        self.assertEqual(self.net.registry.chain(self.X), chain)
        self.assertEqual([self.server_chain_len(s) for s in self.servers], [2, 2, 2, 2])
        # A second round is a no-op.
        self.assertEqual(gossip_round(self.net, store)["pushed"], 0)
        # A fresh participant asking any witness now gets the new chain.
        fresh = RemoteNetwork({self.X: [self.servers[3].url]})
        self.assertEqual(fresh.registry.latest(self.X)["version"], 1)

    def test_equivocation_proof_spreads_and_wallet_stops_counting_the_witness(self):
        cheat = self.ws[0]
        proof = self.equivocation(cheat)
        status, reply = post(self.servers[1].url, {"proofs": [proof]})
        self.assertEqual((status, reply["ok"]["proofs"]), (200, 1))

        alice, carol, dave = (Wallet(n, self.net, self.X) for n in ("alice", "carol", "dave"))
        store = GossipStore(self.net.registry)
        gossip_round(self.net, store)
        for s in self.servers:  # every witness now serves the proof
            self.assertEqual(RemoteWitness(s.url).proofs()["proofs"], [proof])
        self.assertEqual(store.apply(carol.policy), 1)
        self.assertEqual(carol.policy.convicted, {cheat.pk})
        self.assertEqual(store.apply(carol.policy), 0)

        # With witness 3 down, a seal has exactly a quorum (3 of 4) including the cheat.
        usd = alice.issue("USD", 100)
        self.servers[3].stop()
        alice.pay(dave, usd, 10)                      # dave convicted no one: accepts
        with self.assertRaises(InvalidDossier):       # carol does not count the cheat's vote
            alice.pay(carol, usd, 10)
        seal = next(iter(dave.dossier.seals.values()))
        self.assertTrue(verify_seal(seal, self.net.registry))
        self.assertFalse(verify_seal(seal, self.net.registry, carol.policy.convicted))

    def test_equivocations_found_in_votes(self):
        p = self.equivocation(self.ws[2])
        honest = self.ws[1]._vote("11" * 32, 0, "aa" * 32)
        forged = dict(p["b"], sig="00" * 64)
        found = equivocations_in([p["a"], honest, forged, p["b"], p["b"]])
        self.assertEqual(len(found), 1)
        self.assertTrue(verify_equivocation(found[0]))

    def test_bogus_proofs_are_rejected_and_do_not_spread(self):
        w = self.ws[0]
        good = self.equivocation(w)
        outsider = Network()
        Y = outsider.create_constellation("throwaway")  # a valid proof against a key in no charter we know
        bogus = [
            {"a": good["a"], "b": dict(good["b"], sig=good["a"]["sig"])},  # bad signature
            {"a": good["a"], "b": good["a"]},                               # same transition
            {"a": good["a"], "b": self.ws[1]._vote("11" * 32, 0, "bb" * 32)},  # two different witnesses
            self.equivocation(outsider.all_witnesses(Y)[0]),
            {"a": "x"}, 5, None,
        ]
        status, reply = post(self.servers[0].url, {"proofs": bogus})
        self.assertEqual((status, reply["ok"]["proofs"]), (200, 0))
        gossip_round(self.net, GossipStore(self.net.registry))
        for s in self.servers:
            self.assertEqual(RemoteWitness(s.url).proofs()["proofs"], [])

    def test_forged_charter_is_rejected_and_does_not_spread(self):
        weak = self.next_charter(self.ws[:2])                     # 2 of 4: not a quorum
        status, reply = post(self.servers[0].url, {"charters": {self.X: self.sim.registry.chain(self.X) + [weak]}})
        self.assertEqual((status, reply["ok"]["charters"]), (200, 0))
        fake_genesis = charter_body("orion", 0, ["aa" * 32], None)
        post(self.servers[0].url, {"charters": {self.X: [{"body": fake_genesis, "sigs": {}}]}})
        gossip_round(self.net, GossipStore(self.net.registry))
        self.assertEqual([self.server_chain_len(s) for s in self.servers], [1, 1, 1, 1])
        self.assertEqual(self.net.registry.latest(self.X)["version"], 0)

    def test_fork_is_not_adopted_but_its_evidence_spreads(self):
        genesis = self.sim.registry.chain(self.X)
        a = self.next_charter(self.ws[:3], new_keys=[KeyPair.generate() for _ in range(4)])
        b = self.next_charter(self.ws[1:], new_keys=[KeyPair.generate() for _ in range(4)])
        self.servers[0].witness.registry.add_chain(self.X, genesis + [a])
        self.servers[1].witness.registry.add_chain(self.X, genesis + [b])

        store = GossipStore(self.net.registry)
        gossip_round(self.net, store)
        self.assertIn(self.X, store.forks)
        f = store.forks[self.X]
        self.assertTrue(verify_fork(f))
        self.assertEqual(fork_signers(f), {self.ws[1].pk, self.ws[2].pk})  # signed both branches
        # Nobody switched branches; the evidence reached every witness.
        self.assertEqual(self.servers[0].witness.registry.chain(self.X), genesis + [a])
        self.assertEqual(self.servers[1].witness.registry.chain(self.X), genesis + [b])
        for s in self.servers:
            forks = RemoteWitness(s.url).proofs()["forks"]
            self.assertEqual(len(forks), 1)
            self.assertTrue(verify_fork(forks[0]))
        # Forged fork evidence (one branch not quorum-signed) is refused.
        other = GossipStore(Registry())
        forged = dict(f, b=self.next_charter(self.ws[:1], new_keys=[KeyPair.generate()]))
        self.assertFalse(other.add_fork(forged))
        self.assertFalse(other.add_fork(dict(f, b=f["a"])))
        self.assertTrue(other.add_fork(f))

    def test_same_charter_with_other_signatures_is_not_a_fork(self):
        genesis = self.sim.registry.chain(self.X)
        v1a, v1b = self.next_charter(self.ws[:3]), self.next_charter(self.ws[1:])
        store = GossipStore(Registry())
        self.assertTrue(store.add_chain(self.X, genesis + [v1a]))
        self.assertFalse(store.add_chain(self.X, genesis + [v1b]))
        v2 = {"body": charter_body("orion", 2, [w.pk for w in self.ws], charter_hash(v1b["body"])),
              "sigs": {}}
        v2["sigs"] = {w.pk: sign_charter(w.kp, v2["body"]) for w in self.ws}
        self.assertTrue(store.add_chain(self.X, genesis + [v1b, v2]))  # extends ours despite other sigs
        self.assertEqual(store.registry.latest(self.X)["version"], 2)
        self.assertEqual(store.forks, {})

    def test_size_caps(self):
        url = self.servers[0].url
        proof = self.equivocation(self.ws[0])
        for body in ({"proofs": [proof] * (G.MAX_PROOFS + 1)},
                     {"forks": [{}] * (G.MAX_FORKS + 1)},
                     {"charters": {str(i): [] for i in range(G.MAX_CHARTERS + 1)}},
                     {"charters": {self.X: [{}] * (G.MAX_CHAIN + 1)}},
                     {"proofs": "x"}, {"charters": []}):
            status, reply = post(url, body)
            self.assertEqual((status, reply["error"]), (400, "bad_request"))
        self.assertEqual(RemoteWitness(url).proofs()["proofs"], [])
        status, reply = post(url, {"proofs": [proof] * G.MAX_PROOFS})  # at the cap: fine, deduplicated
        self.assertEqual((status, reply["ok"]["proofs"]), (200, 1))

        # New constellations are capped per store; extensions of known ones are not.
        store = GossipStore(Registry(), max_constellations=1)
        self.assertTrue(store.add_chain(self.X, self.sim.registry.chain(self.X)))
        g = charter_body("other", 0, ["aa" * 32], None)
        self.assertFalse(store.add_chain(constellation_id(g), [{"body": g, "sigs": {}}]))
        self.assertTrue(store.add_chain(self.X, self.sim.registry.chain(self.X) + [self.next_charter(self.ws[:3])]))

        # Pushes larger than one message are split into capped batches.
        msg = {"proofs": list(range(G.MAX_PROOFS * 2 + 1))}
        self.assertEqual([len(m["proofs"]) for m in G.batches(msg)], [G.MAX_PROOFS, G.MAX_PROOFS, 1])

        # A client never buffers more than its cap from a peer.
        client = RemoteWitness(url)
        client.max_response = 10
        with self.assertRaises(Unreachable):
            client.pull()

    def test_unreachable_peers_are_skipped(self):
        proof = self.equivocation(self.ws[3])
        post(self.servers[0].url, {"proofs": [proof]})
        self.servers[2].stop()
        out = gossip_round(self.net, GossipStore(self.net.registry))
        self.assertEqual(out["peers"], 3)
        self.assertEqual(len(RemoteWitness(self.servers[1].url).proofs()["proofs"]), 1)
        with self.assertRaises(Rejected):
            RemoteWitness(self.servers[2].url)


if __name__ == "__main__":
    unittest.main()
