"""Scenario 3: a wallet owner tries to spend one parcel twice (manual equivocation).

The witnesses (Rust and Python in one constellation) surface the conflict with
the first vote, the second spend never seals, and holders reject it.
"""

import json
import shutil
import threading
import unittest

from sigil import model, wallet_store
from sigil.proofs import verify_vote
from sigil.validate import InvalidDossier
from sigil.wallet import SealFailed, Wallet, request_seal
from sigil.witness import Conflict, Rejected
from tests.integration.harness import MIXED, IntegrationCase, manual_spend


class DoubleSpendTests(IntegrationCase):
    def setUp(self):
        super().setUp()
        self.X, self.idx = self.c.constellation("orion", MIXED)
        self.write_directory(self.c.directory())

    def test_restored_backup_cannot_spend_again(self):
        X = self.X
        for who in ("alice", "bob", "carol"):
            self.cli(who, "init", "--home", X, "--name", who)
        coin = self.cli("alice", "issue", "COIN", "50")["asset"]
        shutil.copytree(self.wpath("alice"), self.wpath("mallory"))   # alice keeps a backup ...
        pay1, r1 = self.cli_pay("alice", "bob", coin, 50)               # ... pays bob ...
        self.cli("bob", "receive", pay1)
        first_seal = next(s for s in self.load_wallet("bob").dossier.seals.values() if s["tid"] == r1["tid"])

        # ... and restores the backup to pay carol with the same parcel. The honest wallet asks
        # the witnesses first and refuses to sign (SPEC §4 rule 6).
        err = self.cli("mallory", "pay", self.address_file("carol"), coin, 50, "--out", self.file("x.json"), ok=False)
        self.assertEqual(err["error"], "ValueError")
        self.assertIn("equivocate", err["message"])

        # The owner signs the second spend by hand: every witness answers Conflict with the
        # vote it gave bob's payment, byte for byte, and nothing seals.
        m = wallet_store.load(self.wpath("mallory"), self.net())
        refs, _ = m.select(coin, 50)
        addr = self.cli("carol", "address")
        header2, body2, unlocks2, reqs = manual_spend(m, refs, [model.parcel(X, coin, 50, addr["lock"], addr["salt"])])
        with self.assertRaises(SealFailed) as e:
            request_seal(m.network, reqs[0])
        self.assertEqual(len(e.exception.conflicts), 4)
        by_witness = {v["witness"]: v for v in first_seal["votes"]}
        for v in e.exception.conflicts:
            self.assertTrue(verify_vote(v))
            self.assertEqual(v["tid"], r1["tid"])
            if v["witness"] in by_witness:
                self.assertEqual(v["sig"], by_witness[v["witness"]]["sig"])
        for w in m.network.witnesses(X):
            st = w.status(reqs[0]["sigil"])
            self.assertEqual((st["gen"], st["tid"]), (0, r1["tid"]))
            self.assertEqual({v["tid"] for v in st["votes"]}, {r1["tid"]}, w)

        # carol is handed the second spend anyway, with the only "seal" mallory can build (from
        # the conflict votes, which are for bob's transaction): she rejects it.
        tid2 = m.dossier.add_transition(header2, body2, unlocks2)
        d = m.dossier.ancestry([tid2])
        d.add_seal(model.seal_from_votes(e.exception.conflicts))
        bad = self.file("double.json")
        with open(bad, "w") as f:
            json.dump({"dossier": json.loads(d.to_json()), "refs": [model.ref(tid2, 0)]}, f)
        self.assertEqual(self.cli("carol", "receive", bad, ok=False)["error"], "InvalidDossier")
        self.assertEqual(self.cli_balance("carol", coin), 0)

        # bob's money is unaffected: he pays carol, who deep-confirms it.
        pay2, _ = self.cli_pay("bob", "carol", coin, 20)
        self.cli("carol", "receive", pay2, "--deep")
        self.assertEqual((self.cli_balance("bob", coin), self.cli_balance("carol", coin)), (30, 20))
        self.check_invariants({w: self.load_wallet(w) for w in ("alice", "mallory", "bob", "carol")},
                              headers=[header2], stale={"mallory": 1})

    def test_concurrent_conflicting_spends_never_both_seal(self):
        X = self.X
        net = self.net()
        mallory, bob, carol = (Wallet(n, net, X) for n in ("mallory", "bob", "carol"))
        coins = [mallory.issue(f"C{i}", 7) for i in range(3)]
        headers, outcome = [], []
        for coin in coins:
            refs, _ = mallory.select(coin, 7)
            b, c = bob.address(), carol.address()
            h1, b1, u1, r1 = manual_spend(mallory, refs, [model.parcel(X, coin, 7, b["lock"], b["salt"])])
            h2, b2, u2, r2 = manual_spend(mallory, refs, [model.parcel(X, coin, 7, c["lock"], c["salt"])])
            headers += [h1, h2]
            votes = {1: [], 2: []}
            # Both requests reach every witness at the same moment, from two clients.
            for w in net.witnesses(X):
                gate = threading.Barrier(2)

                def send(tag, req, w=w, gate=gate):
                    gate.wait(10)
                    try:
                        votes[tag].append(w.spend(req[0]))
                    except (Conflict, Rejected):
                        pass

                ts = [threading.Thread(target=send, args=(1, r1)), threading.Thread(target=send, args=(2, r2))]
                for t in ts:
                    t.start()
                for t in ts:
                    t.join(30)
            # Each witness voted exactly once.
            self.assertEqual(len(votes[1]) + len(votes[2]), 4)
            for w in net.witnesses(X):
                self.assertEqual(len([v for v in w.status(r1[0]["sigil"])["votes"] if v["gen"] == 0]), 1)
            sealed = [tag for tag in (1, 2) if len(votes[tag]) >= 3]
            self.assertLessEqual(len(sealed), 1)
            outcome.append(sealed)
            # A sealed side is a valid payment its payee accepts; the other side is rejected.
            for tag, (h, bd, u, payee) in ((1, (h1, b1, u1, bob)), (2, (h2, b2, u2, carol))):
                tid = mallory.dossier.add_transition(h, bd, u) if tag in sealed else model.transition_id(h)
                d = mallory.dossier.ancestry([refs[0]["tx"]])
                d.add_transition(h, bd, u)
                if votes[tag]:
                    d.add_seal(model.seal_from_votes(votes[tag]))
                if tag in sealed:
                    payee.receive(d, [model.ref(tid, 0)])
                else:
                    with self.assertRaises(InvalidDossier):
                        payee.receive(d, [model.ref(tid, 0)])
        stale = sum(1 for s in outcome if s)
        # The parcels mallory's wallet still lists: those a race sealed are gone at the witnesses.
        self.check_invariants({"mallory": mallory, "bob": bob, "carol": carol}, headers=headers,
                              stale={"mallory": stale})

    @unittest.expectedFailure
    def test_replayed_payment_rejected_while_home_mostly_unreachable(self):
        """BUG (wallet receive, high for merchants: double credit): a payment the payee already
        received *and spent* is credited again when most of its home's witnesses do not answer.

        Scenario: alice pays bob with a parcel homed in B; bob receives it (CLI) and spends it
        to carol. Later three of B's four witnesses are unreachable from bob (crash, partition,
        or a network attacker between bob and B), and alice hands bob the same old payment file
        again as payment for something else. ``Wallet.receive`` verifies the dossier (valid),
        the address (bob issued it), that bob holds no parcel with that sigil (he spent it),
        and that "at most f witnesses report a binding" -- but it counts only the witnesses
        that answered, and one answering witness reporting the binding is <= f = 1. The CLI
        prints ``received`` and ``balance`` shows 30 more, backed by a consumed parcel that
        can never be spent. (With all four unreachable the check is vacuous.)

        Suggested fix: fail closed in ``Wallet.receive``: require STATUS answers from at least
        a quorum (n - f) of the home's current members, none of them reporting a binding, else
        raise "cannot confirm the parcel is unspent" (retryable); and refuse a parcel whose
        sigil is an input of a transition in the wallet's own dossier (bob's own spend proves
        it consumed without asking anyone).
        """
        c = self.c
        B, b_idx = c.constellation("lyra", ["python", "rust", "rust", "python"])
        self.write_directory(c.directory())
        self.cli("alice", "init", "--home", self.X)
        self.cli("bob", "init", "--home", B)
        self.cli("carol", "init", "--home", self.X)
        usd = self.cli("alice", "issue", "USD", "100")["asset"]
        pay1, _ = self.cli_pay("alice", "bob", usd, 30)                 # homed in B
        self.cli("bob", "receive", pay1)
        pay2, _ = self.cli_pay("bob", "carol", usd, 30)                 # bob spends it
        self.cli("carol", "receive", pay2)
        self.assertEqual(self.cli("bob", "receive", pay1, ok=False)["error"], "InvalidDossier")  # B is up
        for i in b_idx[1:]:
            c.kill(i)
        self.assertEqual(self.cli("bob", "receive", pay1, ok=False)["error"], "InvalidDossier")
