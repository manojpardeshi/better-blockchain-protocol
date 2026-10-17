import unittest

from sigil import KeyPair, Network, SealFailed, Wallet
from sigil import model
from sigil.charter import charter_body, charter_hash
from sigil.swap import propose_swap
from sigil.wallet import request_seal
from sigil.witness import CONTESTED, Conflict, Rejected, Witness
from tests.test_security import manual_spend


class RecoveryTests(unittest.TestCase):
    """An honest party must never lose a parcel to a counter-party's equivocation."""

    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.Y = self.net.create_constellation("lyra")
        self.alice = Wallet("alice", self.net, self.X)
        self.mallory = Wallet("mallory", self.net, self.Y)
        self.bob = Wallet("bob", self.net, self.X)
        self.usd = self.alice.issue("USD", 100)
        self.gold = self.mallory.issue("GOLD", 10)

    def _swap_and_betray(self):
        header, body, _ = propose_swap(self.alice, self.usd, 100, self.mallory, self.gold, 10)
        unlocks = {**self.alice.authorise(header, body), **self.mallory.authorise(header, body)}
        me = self.mallory.address()
        betrayal = manual_spend(self.mallory, [body["inputs"][1]], [model.parcel(self.Y, self.gold, 10, me["lock"], me["salt"])])
        return header, body, unlocks, betrayal

    def test_release_after_counterparty_double_spends(self):
        header, body, unlocks, (_, _, _, reqs) = self._swap_and_betray()
        request_seal(self.net, reqs[0])               # Mallory seals her input elsewhere first
        with self.assertRaises(SealFailed):
            self.alice.seal(header, body, unlocks)    # Alice's input is now bound to a dead swap
        released = self.alice.abort(header)
        self.assertEqual(len(released), 1)
        self.alice.pay(self.bob, self.usd, 100)       # spent again, at generation 1
        self.assertEqual(self.bob.balance(self.usd), 100)

    def test_release_with_split_votes(self):
        """Mallory splits her witnesses so *nothing* is sealed; a quorum of other votes still proves death."""
        header, body, unlocks, (_, _, _, reqs) = self._swap_and_betray()
        me = self.mallory.address()
        _, _, _, reqs2 = manual_spend(self.mallory, [body["inputs"][1]],
                                      [model.parcel(self.Y, self.gold, 10, me["lock"], me["salt"])], memo="again")
        wy = self.net.witnesses(self.Y)
        wy[0].spend(reqs[0]); wy[1].spend(reqs[0])
        wy[2].spend(reqs2[0]); wy[3].spend(reqs2[0])
        with self.assertRaises(SealFailed):
            self.alice.seal(header, body, unlocks)
        self.assertEqual(len(self.alice.abort(header)), 1)
        self.alice.pay(self.bob, self.usd, 40)

    def test_cannot_release_a_live_transition(self):
        header, body, unlocks, _ = self._swap_and_betray()
        self.alice.seal(header, body, unlocks)  # the swap completes
        with self.assertRaises(ValueError):
            self.alice.abort(header)

    def test_witness_rejects_bogus_death_proof(self):
        header, body, unlocks, (_, _, _, reqs) = self._swap_and_betray()
        alice_sigil = header["inputs"][0][0]
        p = self.alice.dossier.output(body["inputs"][0])
        w = self.net.witnesses(self.X)[0]
        w.spend({"sigil": alice_sigil, "header": header, "home": p["home"], "lock": p["lock"],
                 "salt": p["salt"], "unlock": unlocks[alice_sigil]})
        mallory_sigil = header["inputs"][1][0]
        votes = [self.net.witnesses(self.Y)[0].spend(reqs[0])]  # one vote is not a quorum
        with self.assertRaises(Rejected):
            w.release(alice_sigil, {"kind": "votes", "sigil": mallory_sigil, "gen": 0, "votes": votes})


class RotationTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.X)
        self.carol = Wallet("carol", self.net, self.X)
        self.usd = self.alice.issue("USD", 100)

    def _rotate(self, keep=2):
        old = self.net.witnesses(self.X)
        new = [w.kp for w in old[:keep]] + [KeyPair.generate() for _ in range(4 - keep)]
        return old, self.net.rotate(self.X, new)

    def test_parcels_survive_rotation(self):
        self.alice.pay(self.bob, self.usd, 60)
        _, v = self._rotate(keep=0)
        self.assertEqual(v, 1)
        self.bob.pay(self.carol, self.usd, 60)       # sealed by an entirely new witness set
        dave = Wallet("dave", self.net, self.X)
        self.carol.pay(dave, self.usd, 60)
        self.assertEqual(dave.balance(self.usd), 60)

    def test_spent_sigils_stay_spent(self):
        refs, _ = self.alice.select(self.usd, 100)
        b, c = self.bob.address(), self.carol.address()
        _, _, _, r1 = manual_spend(self.alice, refs, [model.parcel(self.X, self.usd, 100, b["lock"], b["salt"])])
        _, _, _, r2 = manual_spend(self.alice, refs, [model.parcel(self.X, self.usd, 100, c["lock"], c["salt"])])
        request_seal(self.net, r1[0])
        old, _ = self._rotate(keep=0)
        with self.assertRaises(SealFailed) as ctx:
            request_seal(self.net, r2[0])
        self.assertEqual(len(ctx.exception.conflicts), 0)  # adopted bindings have no v1 vote yet
        request_seal(self.net, r1[0])  # but the original spend can still be re-attested
        for w in old:
            with self.assertRaises(Rejected):
                w.spend(r2[0])         # frozen witnesses never vote again

    def test_equivocation_before_rotation_is_contested(self):
        refs, _ = self.alice.select(self.usd, 100)
        b, c = self.bob.address(), self.carol.address()
        _, _, _, r1 = manual_spend(self.alice, refs, [model.parcel(self.X, self.usd, 100, b["lock"], b["salt"])])
        _, _, _, r2 = manual_spend(self.alice, refs, [model.parcel(self.X, self.usd, 100, c["lock"], c["salt"])])
        ws = self.net.witnesses(self.X)
        ws[0].spend(r1[0]); ws[1].spend(r1[0]); ws[2].spend(r2[0]); ws[3].spend(r2[0])
        self._rotate(keep=1)
        s = r1[0]["sigil"]
        for w in self.net.witnesses(self.X):
            self.assertEqual(w.records[s].tid, CONTESTED)
            for r in (r1, r2):
                with self.assertRaises(Conflict):
                    w.spend(r[0])

    def test_lying_predecessor_cannot_invent_bindings(self):
        """Forged evidence (no valid owner authorisation) is ignored on adoption."""
        old = self.net.witnesses(self.X)
        fake_sigil = "ab" * 32
        nxt_keys = [KeyPair.generate() for _ in range(4)]
        cur = self.net.registry.latest(self.X)
        nxt = charter_body(cur["name"], 1, [k.pk for k in nxt_keys], charter_hash(cur))
        snaps = []
        sigs = {}
        for w in old:
            sig, snap = w.freeze(nxt)
            sigs[w.pk] = sig
            snaps.append(snap)
        snaps[0][fake_sigil] = [{"kind": "bind", "gen": 0, "auth": {"header": {"inputs": [[fake_sigil, 0]], "body": "00"}}}]
        snaps[1][fake_sigil] = [{"kind": "release", "gen": 5, "tid": "00", "header": {}, "proof": {}}]
        self.net.registry.add_chain(self.X, self.net.registry.chain(self.X) + [{"body": nxt, "sigs": sigs}])
        w = Witness(nxt_keys[0], self.net.registry, self.net.clock)
        w.adopt(self.X, 1, snaps)
        self.assertEqual((w.records[fake_sigil].gen, w.records[fake_sigil].tid), (0, None))


if __name__ == "__main__":
    unittest.main()
