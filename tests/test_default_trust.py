"""A wallet trusts only what its owner configured, never what the network merely learned.

Gossip admits any valid genesis chain from anyone (a genesis needs no signatures), and an
honest witness then serves it from ``/v0/charters``. Before: ``RemoteNetwork`` added every
chain a witness served to its registry, and ``Wallet`` trusted every constellation in the
registry by default, so an outsider could make default-configured wallets trust a
constellation whose every key it holds, move a real asset's parcel there and double-spend it
to two such wallets (the outputs live in an honest home, so their STATUS checks pass).
"""

import json
import os
import tempfile
import unittest
import urllib.request

from sigil import Network, Wallet, locks, model, wallet_store
from sigil.charter import Registry
from sigil.server import RemoteNetwork, WitnessServer
from sigil.validate import InvalidDossier


def gossip(url: str, msg: dict) -> None:
    req = urllib.request.Request(f"{url}/v0/gossip", data=json.dumps(msg).encode(), method="POST",
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=5) as r:
        r.read()


class DefaultTrust(unittest.TestCase):
    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.servers = []
        for w in self.sim.all_witnesses(self.X):  # separate processes have separate registries
            w.registry = Registry()
            w.registry.add_chain(self.X, self.sim.registry.chain(self.X))
            self.servers.append(WitnessServer(w).start())
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        self.urls = [s.url for s in self.servers]
        # The attacker's constellation: one witness, its key the attacker's.
        self.evil_sim = Network(self.sim.clock)
        self.EVIL = self.evil_sim.create_constellation("evil", n=1)
        self.evil_w = self.evil_sim.all_witnesses(self.EVIL)[0]

    def _plant(self):
        """An outsider (no key of X) gossips the evil genesis to one honest witness of X."""
        gossip(self.urls[0], {"charters": {self.EVIL: self.evil_sim.registry.chain(self.EVIL)}})
        self.assertIn(self.EVIL, self.servers[0].witness.registry)

    def test_gossiped_constellation_is_not_trusted_or_learned(self):
        self._plant()
        net = RemoteNetwork({self.X: self.urls})
        self.assertNotIn(self.EVIL, net.registry, "refresh_charters admitted a chain it did not ask for")
        bob = Wallet("bob", net, self.X)
        self.assertEqual(bob.policy.trusted, {self.X})

    def test_double_spend_through_a_planted_constellation(self):
        """The whole attack: before, bob and carol (default trust) both accepted the same value."""
        self._plant()
        # The attacker's wallet reaches X over HTTP and its own constellation in-process.
        mnet = RemoteNetwork({self.X: self.urls})
        mnet.registry.add_chain(self.EVIL, self.evil_sim.registry.chain(self.EVIL))
        mallory = Wallet("mallory", mnet, self.X, trusted={self.X, self.EVIL}, clock=self.sim.clock)
        usd = mallory.issue("USD", 100)
        # Move the real asset's parcel to a home the attacker controls (X seals it honestly).
        a = mallory.address(self.EVIL)
        coin = next(iter(mallory.holdings.values()))
        tid0 = mallory.transact([coin["ref"]], [model.parcel(self.EVIL, usd, 100, a["lock"], a["salt"])])
        ref, p = model.ref(tid0, 0), mallory.dossier.output(model.ref(tid0, 0))
        s, kp = model.sigil_of(p), mallory.keys[a["lock"]["pk"]]
        accepted = []
        for name in ("bob", "carol"):
            victim = Wallet(name, RemoteNetwork({self.X: self.urls}), self.X, clock=self.sim.clock)
            to = victim.address(self.X)
            body = model.body([ref], [model.parcel(self.X, usd, 100, to["lock"], to["salt"])], memo=name)
            header = model.header([[s, 0]], body)
            tid = model.transition_id(header)
            exp = int(self.sim.clock()) + 600
            u = locks.empty_unlock(exp)
            u["sigs"][kp.pk] = locks.sign_unlock(kp, s, tid, exp)
            d = mallory.dossier.ancestry([tid0])
            d.add_transition(header, body, {s: u})
            d.add_seal(model.seal_from_votes([self.evil_w._vote(s, 0, tid)]))  # the attacker equivocates
            d.add_charters(mnet.registry, [self.X, self.EVIL])
            try:
                victim.receive(d, [model.ref(tid, 0)])
                accepted.append(name)
            except InvalidDossier:
                pass
        self.assertEqual(accepted, [], "a planted constellation let one parcel pay two default wallets")

    def test_cli_and_store_defaults(self):
        """``sigil init`` and a wallet saved before the trust policy existed trust only the directory."""
        self._plant()
        d = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__("shutil").rmtree(d, ignore_errors=True))
        directory = os.path.join(d, "dir.json")
        with open(directory, "w") as f:
            json.dump({self.X: self.urls}, f)
        from sigil import cli
        cli.main(["--wallet", os.path.join(d, "w"), "--directory", directory, "init", "--name", "w",
                  "--home", self.X])
        w = wallet_store.load(os.path.join(d, "w"), RemoteNetwork({self.X: self.urls}))
        self.assertEqual(w.policy.trusted, {self.X})
        state = os.path.join(d, "w", "state.json")
        with open(state) as f:
            st = json.load(f)
        del st["trusted"]  # a wallet from before the trust policy was saved
        with open(state, "w") as f:
            json.dump(st, f)
        w = wallet_store.load(os.path.join(d, "w"), RemoteNetwork({self.X: self.urls}))
        self.assertEqual(w.policy.trusted, {self.X})

    def test_a_witness_filled_with_chains_still_serves_ours(self):
        """Before (since replies were capped): anyone could gossip ~300 genesis charters of
        ~60 KiB to every honest witness, so ``/v0/charters`` outgrew the 16 MiB a client reads
        and a fresh ``RemoteNetwork`` learned no chain at all. A client now asks for the chain
        of each constellation it is configured with (``GET /v0/charters/<cid>``)."""
        from sigil.charter import charter_body, constellation_id
        from sigil.crypto import KeyPair
        from sigil.gossip import GossipStore, gossip_round
        from sigil.server import MAX_RESPONSE
        pks = [KeyPair.generate().pk for _ in range(4)]
        total, batch = 0, {}
        for i in range(300):
            g = charter_body(f"{i:04d}" + "n" * 60_000, 0, pks, None)
            batch[constellation_id(g)] = [{"body": g, "sigs": {}}]
            total += 60_000
            if len(batch) == 15:
                for url in self.urls:
                    gossip(url, {"charters": batch})
                batch = {}
        self.assertGreater(total, MAX_RESPONSE)
        net = RemoteNetwork({self.X: self.urls})
        self.assertIn(self.X, net.registry)
        self.assertEqual(Wallet("bob", net, self.X).policy.trusted, {self.X})
        # Gossip rounds still carry the chains of the constellations the network is configured with.
        store = GossipStore(Registry())
        gossip_round(net, store)
        self.assertIn(self.X, store.registry)

    def test_configured_constellations_are_trusted(self):
        """Every constellation of the directory (and the home) is still trusted by default."""
        Y = self.sim.create_constellation("lyra")
        ys = [WitnessServer(w).start() for w in self.sim.all_witnesses(Y)]
        self.addCleanup(lambda: [s.stop() for s in ys])
        net = RemoteNetwork({self.X: self.urls, Y: [s.url for s in ys]})
        self.assertEqual(Wallet("bob", net, self.X).policy.trusted, {self.X, Y})
        self.assertIn(Y, net.registry)


if __name__ == "__main__":
    unittest.main()
