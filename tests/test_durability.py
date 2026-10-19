import copy
import itertools
import os
import tempfile
import unittest

from sigil import Network, SealFailed, Wallet
from sigil import model
from sigil.charter import charter_body, charter_hash
from sigil.stamps import StampMint, buy_stamp
from sigil.store import WitnessStore
from sigil.swap import propose_swap
from sigil.wallet import find_death_proof, request_seal
from sigil.witness import Conflict, Rejected, Witness
from tests.test_security import manual_spend


class Crash(Exception):
    """Stands in for the process dying."""


class DurableCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.stores: list[WitnessStore] = []
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.net.members[self.X] = [self.durable(w.kp, f"w{i}") for i, w in enumerate(self.net.members[self.X])]
        self.addCleanup(lambda: [s.close() for s in self.stores])

    def durable(self, kp, name: str, **kw) -> Witness:
        """Build a witness on ``name``'s store, joining only if the store is fresh."""
        store = WitnessStore(os.path.join(self.tmp.name, name + ".db"))
        self.stores.append(store)
        w = Witness(kp, self.net.registry, self.net.clock, store=store, **kw)
        if w.cid is None:
            w.join(self.X, 0)
        return w

    def restart(self, w: Witness, name: str, **kw) -> Witness:
        w.store.close()
        return self.durable(w.kp, name, **kw)

    def restart_all(self) -> None:
        self.net.members[self.X] = [self.restart(w, f"w{i}") for i, w in enumerate(self.net.members[self.X])]

    def two_spends(self):
        """Two conflicting single-input requests for the same sigil."""
        alice, bob, carol = (Wallet(n, self.net, self.X) for n in ("alice", "bob", "carol"))
        usd = alice.issue("USD", 100)
        refs, _ = alice.select(usd, 100)
        to_b, to_c = bob.address(), carol.address()
        r1 = manual_spend(alice, refs, [model.parcel(self.X, usd, 100, to_b["lock"], to_b["salt"])])[3][0]
        r2 = manual_spend(alice, refs, [model.parcel(self.X, usd, 100, to_c["lock"], to_c["salt"])])[3][0]
        return r1, r2

    def betrayed_swap(self):
        """Alice's input ends up bound to a swap that Mallory killed; returns (alice, usd, header)."""
        Y = self.net.create_constellation("lyra")
        alice, mallory = Wallet("alice", self.net, self.X), Wallet("mallory", self.net, Y)
        usd, gold = alice.issue("USD", 100), mallory.issue("GOLD", 10)
        header, body, _ = propose_swap(alice, usd, 100, mallory, gold, 10)
        unlocks = {**alice.authorise(header, body), **mallory.authorise(header, body)}
        me = mallory.address()
        betrayal = manual_spend(mallory, [body["inputs"][1]], [model.parcel(Y, gold, 10, me["lock"], me["salt"])])
        request_seal(self.net, betrayal[3][0])
        with self.assertRaises(SealFailed):
            alice.seal(header, body, unlocks)
        return alice, usd, header


class RestartTests(DurableCase):
    def test_vote_survives_restart(self):
        r1, r2 = self.two_spends()
        w = self.net.members[self.X][0]
        v1 = w.spend(r1)
        w = self.restart(w, "w0")
        self.net.clock.advance(3600)  # a fresh vote would carry a different time
        with self.assertRaises(Conflict) as ctx:
            w.spend(r2)
        self.assertEqual(ctx.exception.vote, v1)
        self.assertEqual(w.spend(r1), v1)
        self.assertEqual(w.status(r1["sigil"])["votes"], [v1])

    def test_release_survives_restart(self):
        alice, usd, header = self.betrayed_swap()
        bob = Wallet("bob", self.net, self.X)
        self.assertEqual(len(alice.abort(header)), 1)
        self.restart_all()
        sigil = header["inputs"][0][0]
        for w in self.net.members[self.X]:
            self.assertEqual(w.status(sigil)["gen"], 1)
            self.assertIsNone(w.status(sigil)["tid"])
        alice.pay(bob, usd, 100)  # spendable at generation 1 after the restart
        self.assertEqual(bob.balance(usd), 100)

    def test_frozen_survives_restart(self):
        r1, _ = self.two_spends()
        w = self.net.members[self.X][0]
        cur = self.net.registry.charter(self.X, 0)
        w.freeze(charter_body(cur["name"], 1, cur["witnesses"], charter_hash(cur)))
        w = self.restart(w, "w0")
        self.assertTrue(w.frozen)
        with self.assertRaises(Rejected):
            w.spend(r1)

    def test_redeemed_stamps_survive_restart(self):
        r1, _ = self.two_spends()
        kp, mint = self.net.members[self.X][0].kp, StampMint(1024)
        w = self.durable(kp, "paid", stamp_mint=mint)
        stamp = buy_stamp(mint.public, w.sell_stamp)
        w.spend({**r1, "stamp": stamp})
        reloaded = copy.copy(mint)       # same key, as reloaded by the operator ...
        reloaded._redeemed = set()       # ... but with no memory of redemptions
        w = self.restart(w, "paid", stamp_mint=reloaded)
        with self.assertRaises(Rejected):
            w.spend({**r1, "stamp": stamp})

    def test_store_rejects_other_key(self):
        w0, w1 = self.net.members[self.X][:2]
        w0.store.close()
        with self.assertRaises(ValueError):
            self.durable(w1.kp, "w0")


class CrashTests(DurableCase):
    """A crash at any point around the durable write never lets a restarted witness contradict a vote it released."""

    def crash_on_write(self, w: Witness, mode: str) -> None:
        if mode == "none":
            return
        append = w.store.append

        def crashing(entries):
            if mode == "after":
                append(entries)
            raise Crash

        w.store.append = crashing

    def test_spend_crash_schedules(self):
        r1, r2 = self.two_spends()
        kp = self.net.members[self.X][0].kp
        for n, modes in enumerate(itertools.product(["none", "before", "after"], repeat=3)):
            name = f"sched{n}"
            w = self.durable(kp, name)
            released = {}  # tid -> the vote the outside world saw
            for req, mode in zip([r1, r2, r1], modes):
                self.crash_on_write(w, mode)
                try:
                    v = w.spend(req)
                    released.setdefault(v["tid"], v)
                    self.assertEqual(released[v["tid"]], v)
                except Conflict:
                    pass
                except Crash:
                    # The live process must not have adopted state it failed to persist.
                    self.assertEqual(w.status(req["sigil"])["votes"], list(released.values()), modes)
                w = self.restart(w, name)
            self.assertLessEqual(len(released), 1, modes)  # never two different votes at (sigil, 0)
            for tid, v in released.items():
                same, other = (r1, r2) if model.transition_id(r1["header"]) == tid else (r2, r1)
                self.assertEqual(w.spend(same), v, modes)
                with self.assertRaises(Conflict, msg=modes):
                    w.spend(other)

    def test_release_crash(self):
        alice, _, header = self.betrayed_swap()
        sigil = header["inputs"][0][0]
        proof = find_death_proof(self.net, header, model.transition_id(header), alice._parcels_for(header))
        for i, mode in enumerate(("before", "after")):
            w = self.net.members[self.X][i]
            self.crash_on_write(w, mode)
            with self.assertRaises(Crash):
                w.release(sigil, proof)
            self.assertEqual(w.status(sigil)["gen"], 0)  # unpersisted release is not adopted
            w = self.restart(w, f"w{i}")
            self.assertEqual(w.status(sigil)["gen"], 1 if mode == "after" else 0)

    def test_freeze_crash(self):
        r1, _ = self.two_spends()
        kp = self.net.members[self.X][0].kp
        cur = self.net.registry.charter(self.X, 0)
        nxt = charter_body(cur["name"], 1, cur["witnesses"], charter_hash(cur))
        for mode in ("before", "after"):
            w = self.durable(kp, "freeze-" + mode)
            w.spend(r1)
            self.crash_on_write(w, mode)
            with self.assertRaises(Crash):
                w.freeze(nxt)
            self.assertFalse(w.frozen)  # no response was given, so the live witness stays active
            w = self.restart(w, "freeze-" + mode)
            self.assertEqual(w.frozen, mode == "after")
            if not w.frozen:  # a vote is still the same vote
                self.assertEqual(w.spend(r1), w.status(r1["sigil"])["votes"][0])


if __name__ == "__main__":
    unittest.main()
