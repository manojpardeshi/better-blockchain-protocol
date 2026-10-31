"""Rotation over the wire (/v0/freeze, /v0/adopt, RemoteNetwork.rotate) and its hardening.

bench/interop.py runs the same flows against Rust witness processes; these tests pin the
reference's own server.
"""

import unittest

from sigil import Network, Wallet, locks, model
from sigil.charter import Registry, charter_body, charter_hash
from sigil.crypto import KeyPair
from sigil.gossip import GossipStore
from sigil.proofs import verify_seal
from sigil.server import RemoteNetwork, RemoteWitness, WitnessServer
from sigil.witness import CONTESTED, Conflict, Rejected, Witness

TOKEN = "t0ken"


class RotationOverHttp(unittest.TestCase):
    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.old = self.sim.all_witnesses(self.X)
        for w in self.old:  # separate processes have separate registries
            w.registry = Registry()
            w.registry.add_chain(self.X, self.sim.registry.chain(self.X))
        self.servers = [WitnessServer(w, admin_token=TOKEN).start() for w in self.old]
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        self.net = RemoteNetwork({self.X: [s.url for s in self.servers]})

    def new_members(self, keys) -> list:
        """Fresh witnesses that have joined nothing (``witnessd run --adopt``)."""
        urls = []
        for kp in keys:
            reg = Registry()
            reg.add_chain(self.X, self.sim.registry.chain(self.X))
            s = WitnessServer(Witness(kp, reg, self.sim.clock), admin_token=TOKEN).start()
            self.servers.append(s)
            urls.append(s.url)
        return urls

    def test_rotate_carries_bindings_and_payments_continue(self):
        alice, bob = Wallet("alice", self.net, self.X), Wallet("bob", self.net, self.X)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 40)
        reused = self.old[0].kp
        urls = self.new_members([reused] + [KeyPair.generate() for _ in range(3)])
        self.assertIsNone(RemoteWitness(urls[1]).cid)
        self.assertEqual(self.net.rotate(self.X, urls, TOKEN), 1)
        self.assertTrue(all(w.frozen for w in self.old))
        self.assertEqual([w.version for w in self.net.witnesses(self.X)], [1, 1, 1, 1])
        bob.pay(alice, usd, 15)
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (75, 25))
        carol = Wallet("carol", RemoteNetwork({self.X: urls}), self.X, deep_threshold=1)
        alice.pay(carol, usd, 5)
        self.assertEqual(carol.balance(usd), 5)

    def test_rotation_calls_need_the_token_and_adopt_runs_once(self):
        cur = self.sim.registry.latest(self.X)
        nxt = charter_body("orion", 1, [KeyPair.generate().pk], charter_hash(cur))
        for token in (None, "nope"):
            with self.assertRaises(Rejected):
                RemoteWitness(self.servers[0].url, admin_token=token).freeze(nxt)
        open_server = WitnessServer(self.old[1]).start()      # no admin token configured
        self.addCleanup(open_server.stop)
        with self.assertRaises(Rejected):
            RemoteWitness(open_server.url, admin_token=TOKEN).freeze(nxt)
        self.assertFalse(any(w.frozen for w in self.old))
        urls = self.new_members([KeyPair.generate() for _ in range(4)])
        self.net.rotate(self.X, urls, TOKEN)
        m = RemoteWitness(urls[0], admin_token=TOKEN)
        m.adopt(self.X, 1, [])                                  # a retry answers the same
        with self.assertRaises(Rejected):
            m.adopt(self.X, 2, [])
        with self.assertRaises(Rejected):                       # bad_request: snapshots must be a list
            m._call("adopt", {"constellation": self.X, "version": 1, "snapshots": {}})
        # The second freeze for another successor is refused over the wire too.
        other = charter_body("orion", 1, [KeyPair.generate().pk], charter_hash(cur))
        with self.assertRaises(Rejected):
            RemoteWitness(self.servers[0].url, admin_token=TOKEN).freeze(other)

    def test_regression_contested_over_http(self):
        """RotationRegressionTests' first scenario, driven through the server."""
        owner = KeyPair.generate()
        exp = int(self.sim.clock()) + 10 ** 6

        def mk(salt):
            p = model.parcel(self.X, "x", 1, locks.sig(owner.pk), salt)
            return p, model.sigil_of(p)

        ps, s = mk("s")
        px, x = mk("x")
        tgt = lambda p: {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}  # noqa: E731
        hdr = lambda inputs, tag: {"inputs": [list(i) for i in inputs], "body": tag * 64}  # noqa: E731

        def req(h, sigil, p):
            u = locks.empty_unlock(exp)
            u["sigs"][owner.pk] = locks.sign_unlock(owner, sigil, model.transition_id(h), exp)
            return {"sigil": sigil, "header": h, "home": self.X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

        Ty, Tb, Ta, Tg = hdr([(x, 0)], "1"), hdr([(s, 0), (x, 0)], "2"), hdr([(s, 0)], "3"), hdr([(s, 1)], "4")
        k = self.net.witnesses(self.X)
        seal_y = model.seal_from_votes([w.spend(req(Ty, x, px)) for w in k])
        seal_b = model.seal_from_votes([w.spend(req(Tb, s, ps)) for w in k[:3]])
        k[3].spend(req(Ta, s, ps))
        for w in k[:3]:
            w.release(s, {"kind": "seal", "sigil": x, "gen": 0, "parcel": tgt(px), "seal": seal_y})
        self.net.rotate(self.X, self.new_members([KeyPair.generate() for _ in range(4)]), TOKEN)
        ws = self.net.witnesses(self.X)
        self.assertEqual({w.status(s)["tid"] for w in ws}, {CONTESTED})

        def try_seal(h):
            votes = []
            for w in ws:
                try:
                    votes.append(w.spend(req(h, s, ps)))
                except (Rejected, Conflict):
                    pass
            return votes and verify_seal(model.seal_from_votes(votes), self.net.registry)

        self.assertFalse(try_seal(Ta))
        for w in ws:
            w.release(s, {"kind": "seal", "sigil": s, "gen": 0, "parcel": tgt(ps), "seal": seal_b})
        self.assertTrue(try_seal(Tg))
        self.assertFalse(try_seal(Ta))


class AdoptHardening(unittest.TestCase):
    def test_malformed_snapshots_are_skipped_like_unverifiable_evidence(self):
        net = Network()
        X = net.create_constellation("orion")
        owner = KeyPair.generate()
        p = model.parcel(X, "x", 1, locks.sig(owner.pk), "aa")
        s = model.sigil_of(p)
        h = {"inputs": [[s, 0]], "body": "11" * 32}
        u = locks.empty_unlock(int(net.clock()) + 600)
        u["sigs"][owner.pk] = locks.sign_unlock(owner, s, model.transition_id(h), u["expires"])
        req = {"sigil": s, "header": h, "home": X, "lock": p["lock"], "salt": p["salt"], "unlock": u}
        snaps = []
        cur = net.registry.latest(X)
        new = [KeyPair.generate() for _ in range(4)]
        nxt = charter_body("orion", 1, [k.pk for k in new], charter_hash(cur))
        sigs = {}
        for w in net.all_witnesses(X):
            w.spend(req)
            sigs[w.pk], snap = w.freeze(nxt)
            snaps.append(snap)
        net.registry.add_chain(X, net.registry.chain(X) + [{"body": nxt, "sigs": sigs}])
        bad_auth = {"home": X, "lock": p["lock"], "salt": p["salt"], "header": h, "unlock": 5}
        junk = [5, "x", None, {s: "notalist", "t": [1, "e", {"kind": "bind", "auth": bad_auth}, {"kind": "bind"}]}]
        w = Witness(new[0], net.registry, net.clock)
        w.adopt(X, 1, junk + snaps)
        self.assertEqual(w.records[s].tid, model.transition_id(h))
        self.assertEqual(w.records["t"].tid, None)


class GossipForkCap(unittest.TestCase):
    def test_fork_evidence_is_capped_per_store(self):
        from sigil.charter import sign_charter
        net = Network()
        X = net.create_constellation("orion")
        ws = net.all_witnesses(X)
        chain = net.registry.chain(X)
        cur = chain[-1]["body"]

        def v1(signers):
            b = charter_body("orion", 1, [KeyPair.generate().pk], charter_hash(cur))
            return {"body": b, "sigs": {w.pk: sign_charter(w.kp, b) for w in signers}}

        fork = {"constellation": X, "prefix": chain, "a": v1(ws[:3]), "b": v1(ws[1:])}
        self.assertFalse(GossipStore(Registry(), max_constellations=0).add_fork(fork))
        self.assertTrue(GossipStore(Registry(), max_constellations=1).add_fork(fork))


if __name__ == "__main__":
    unittest.main()
