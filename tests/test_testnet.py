"""A real multi-process testnet: every witness is its own ``sigil.witnessd`` process.

Wallets reach the witnesses only over HTTP, through ``RemoteNetwork`` built
from the testnet's directory.json. The crash harness SIGKILLs a witness
while payments are running, restarts it on the same store and port, and
checks that it remembers every vote it gave (durability across a real
process crash, SPEC §5).
"""

import os
import shutil
import signal
import tempfile
import threading
import unittest

from sigil import Wallet, model
from sigil.server import RemoteNetwork, RemoteWitness
from sigil.swap import atomic_swap
from sigil.witness import Conflict, Rejected
from testnet import Testnet
from tests.test_security import manual_spend


def _testnet(case, constellations: int, witnesses: int, **kw) -> Testnet:
    """Create and start a testnet that is torn down (SIGKILL) even if the test fails."""
    tmp = tempfile.mkdtemp(prefix="sigil-testnet-")
    tn = Testnet(tmp)
    case.addClassCleanup(shutil.rmtree, tmp, ignore_errors=True)
    case.addClassCleanup(tn.stop_all, signal.SIGKILL)
    tn.create(constellations, witnesses, **kw)
    tn.start_all()
    return tn


class TestnetTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tn = _testnet(cls, constellations=2, witnesses=4)
        cls.X, cls.Y = list(cls.tn.directory())

    def network(self) -> RemoteNetwork:
        return RemoteNetwork(self.tn.directory(), timeout=3)

    def test_files_and_key_permissions(self):
        for w in self.tn.witnesses:
            self.assertEqual(os.stat(w["key"]).st_mode & 0o777, 0o600)
        net = self.network()
        for cid in (self.X, self.Y):
            self.assertEqual(len(net.registry.latest(cid)["witnesses"]), 4)
            self.assertEqual(len(net.witnesses(cid)), 4)

    def test_issue_pay_and_swap_across_constellations(self):
        net = self.network()
        alice, bob = Wallet("alice", net, self.X), Wallet("bob", net, self.Y)
        usd, gold = alice.issue("USD", 1_000), bob.issue("GOLD", 10)
        alice.pay(bob, usd, 300)                        # the parcel moves from X to Y
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (700, 300))
        atomic_swap(alice, usd, 100, bob, gold, 2)      # inputs in both constellations
        self.assertEqual((alice.balance(usd), alice.balance(gold)), (600, 2))
        self.assertEqual((bob.balance(usd), bob.balance(gold)), (400, 8))

    def test_crash_restart_keeps_votes_and_payments_continue(self):
        tn, victim = self.tn, 0                          # witness 0 of constellation X
        self.assertEqual(tn.witnesses[victim]["cid"], self.X)
        net = self.network()
        alice, bob, carol = (Wallet(n, net, self.X) for n in ("alice", "bob", "carol"))
        usd = alice.issue("USD", 1_000)

        # The victim votes for one spend of carol's coin before it crashes.
        coin = carol.issue("C", 5)
        refs, _ = carol.select(coin, 5)
        b, a = bob.address(), alice.address()
        *_, r1 = manual_spend(carol, refs, [model.parcel(self.X, coin, 5, b["lock"], b["salt"])])
        *_, r2 = manual_spend(carol, refs, [model.parcel(self.X, coin, 5, a["lock"], a["salt"])])
        client = RemoteWitness(tn.url(victim), timeout=3)
        vote = client.spend(r1[0])

        # SIGKILL the victim from another thread while payments are in flight.
        started, killed = threading.Event(), threading.Event()

        def killer():
            started.wait(30)
            tn.kill(victim, signal.SIGKILL)
            killed.set()

        t = threading.Thread(target=killer, daemon=True)
        t.start()
        after_kill = 0
        for i in range(40):
            alice.pay(bob, usd, 1)                       # must never fail: f=1 is tolerated
            bob.pay(alice, usd, 1)
            if i == 1:
                started.set()
            if killed.is_set():
                after_kill += 1
                if after_kill >= 3:
                    break
        t.join(10)
        self.assertGreaterEqual(after_kill, 3, "payments did not continue with a witness down")
        with self.assertRaises(Rejected):
            client.status(vote["sigil"])                 # really gone

        tn.start(victim)
        tn.wait_ready(victim)

        # Same vote again, byte for byte, and the conflicting spend is refused.
        self.assertEqual(client.spend(r1[0]), vote)
        with self.assertRaises(Conflict) as ctx:
            client.spend(r2[0])
        self.assertEqual(ctx.exception.vote, vote)

        # Every vote of the victim's that went into a seal before the crash is remembered.
        pk = RemoteWitness(tn.url(victim)).pk
        remembered = 0
        for seal in list(alice.dossier.seals.values()) + list(bob.dossier.seals.values()):
            for v in seal["votes"]:
                if v["witness"] == pk:
                    held = {(x["tid"], x["sig"]) for x in client.status(seal["sigil"])["votes"]}
                    self.assertIn((seal["tid"], v["sig"]), held)
                    remembered += 1
        self.assertGreater(remembered, 0)

        # Payments go on with the restarted witness voting again.
        net.down.clear()
        tid = alice.pay(bob, usd, 5)
        sealed_by = {v["witness"] for s in alice.dossier.seals.values() if s["tid"] == tid for v in s["votes"]}
        self.assertIn(pk, sealed_by)


class StampedTestnetTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tn = _testnet(cls, constellations=1, witnesses=1, stamps=True)
        (cls.X,) = cls.tn.directory()

    def test_stamp_key_survives_restart_and_sigterm_is_graceful(self):
        tn = self.tn
        net = RemoteNetwork(tn.directory(), timeout=3)
        alice, bob = Wallet("alice", net, self.X), Wallet("bob", net, self.X)
        coin = alice.issue("C", 10)
        alice.buy_stamps(self.X, 2)
        alice.pay(bob, coin, 1)
        public = RemoteWitness(tn.url(0)).stamps.public

        tn.kill(0, signal.SIGKILL)
        tn.start(0)
        tn.wait_ready(0)
        self.assertEqual(RemoteWitness(tn.url(0)).stamps.public, public)
        alice.pay(bob, coin, 1)                           # a stamp bought before the crash
        self.assertEqual(bob.balance(coin), 2)

        p = tn.procs[0]
        tn.kill(0, signal.SIGTERM)
        self.assertEqual(p.returncode, 0)
        with open(tn.witnesses[0]["log"]) as f:
            self.assertTrue(f.read().rstrip().endswith("stopped"))


if __name__ == "__main__":
    unittest.main()
