"""Scenario 1: the command-line wallet end to end, across two mixed Rust+Python constellations.

Every wallet command runs as its own process (``python -m sigil.cli``); payments
travel between holders only as exported files.
"""

import json
import unittest

from tests.integration.harness import MIXED, IntegrationCase, RemoteWitness


class CliPaymentTests(IntegrationCase):
    def test_cross_home_payments_with_deep_confirmation(self):
        c = self.c
        A, a_idx = c.constellation("orion", MIXED)
        B, b_idx = c.constellation("lyra", ["python", "rust", "python", "rust"])
        self.write_directory(c.directory())
        rust_pks = {RemoteWitness(c.url(i)).pk for i in a_idx + b_idx if c.witnesses[i]["kind"] == "rust"}

        for who, home in (("alice", A), ("bob", B), ("carol", A)):
            self.assertEqual(self.cli(who, "init", "--home", home, "--name", who)["home"], home)
        self.cli("dave", "init", "--home", B, "--name", "dave", "--deep-threshold", "1")
        self.assertEqual(self.cli("dave", "init", "--home", B, ok=False)["error"], "CliError")

        usd = self.cli("alice", "issue", "USD", "1000")["asset"]
        self.assertEqual(self.cli("alice", "assets"), [{"asset": usd, "name": "USD", "balance": 1000}])

        # alice (home A) pays bob, who chose an address in B: the parcel moves A -> B.
        pay1, r = self.cli_pay("alice", "bob", usd, 300)
        self.assertEqual(r["balance"], 700)
        got = self.cli("bob", "receive", pay1, "--deep")
        self.assertEqual(got, {"already": False, "received": [{"asset": usd, "amount": 300, "home": B}]})
        # The seal on alice's input mixes Rust and Python votes of A.
        with open(pay1) as f:
            p = json.load(f)
        seal = next(s for s in p["dossier"]["seals"].values() if s["tid"] == r["tid"])
        voters = {v["witness"] for v in seal["votes"]}
        self.assertTrue(voters & rust_pks and voters - rust_pks, "seal mixes both implementations")
        self.assertGreaterEqual(len(voters), 3)

        # Receiving again is a no-op.
        self.assertEqual(self.cli("bob", "receive", pay1), {"already": True, "received": []})
        # A payment file is no use to anyone but its payee.
        self.assertEqual(self.cli("carol", "receive", pay1, ok=False)["error"], "InvalidDossier")

        pay2, _ = self.cli_pay("bob", "carol", usd, 120)                # B -> A
        self.assertEqual(self.cli("carol", "receive", pay2, "--deep")["received"][0]["amount"], 120)
        # bob has spent pay1's parcel since: replaying it is refused (its sigil is consumed).
        self.assertEqual(self.cli("bob", "receive", pay1, ok=False)["error"], "InvalidDossier")

        pay3, _ = self.cli_pay("carol", "dave", usd, 20)                # A -> B, deep by threshold
        self.cli("dave", "receive", pay3)
        dave = self.load_wallet("dave")
        # Every input in the ancestry (alice->bob, bob->carol, carol->dave) was deep-confirmed
        # against the current members' STATUS, Rust and Python alike.
        self.assertGreaterEqual(len(dave._confirmed), 3)

        pay4, _ = self.cli_pay("dave", "alice", usd, 5)                 # B -> A
        self.cli("alice", "receive", pay4, "--deep")

        # An asset issued into the other constellation: bob (home B) issues GOLD homed in A.
        gold = self.cli("bob", "issue", "GOLD", "50", "--home", A)["asset"]
        pay5, _ = self.cli_pay("bob", "alice", gold, 10)
        self.assertEqual(self.cli("alice", "receive", pay5)["received"], [{"asset": gold, "amount": 10, "home": A}])

        balances = {w: self.cli_balance(w, usd) for w in ("alice", "bob", "carol", "dave")}
        self.assertEqual(balances, {"alice": 705, "bob": 180, "carol": 100, "dave": 15})
        self.assertEqual(self.cli("alice", "balance"), {usd: 705, gold: 10})
        self.assertEqual(sorted(a["name"] for a in self.cli("alice", "assets")), ["GOLD", "USD"])
        exported = self.cli("dave", "export-dossier")
        self.assertIn(usd, exported["transitions"])
        self.assertEqual(set(exported["charters"]), {A, B})

        self.check_invariants({w: self.load_wallet(w) for w in ("alice", "bob", "carol", "dave")})

    def test_address_in_a_home_the_payee_does_not_trust_is_refused(self):
        """BUG (CLI, low-medium: a typo burns the payer's money): ``address --home CID`` hands
        out an address in any home, even one the wallet does not trust or that does not exist.

        Scenario: bob runs ``address --home`` with a mistyped constellation id (or one added to
        the directory after his ``init``, which his saved trust policy does not include; the CLI
        has no command to trust it). alice pays that address: her own home's witnesses seal the
        payment (nobody checks an output's home), and her balance drops. bob's ``receive``
        rejects the parcel ("parcel lives in a constellation we do not trust"). For a home that
        does not exist no witness will ever sign for the parcel, so the amount is gone for good;
        for an untrusted one bob cannot accept it from the CLI.

        Suggested fix: ``cmd_address`` (and ``Wallet.address``) should refuse a home the
        wallet's trust policy does not trust (``policy.trusts(home)``: known charter and
        trusted), with a CliError; optionally add a ``trust CID`` command for the owner's
        explicit decision.
        """
        A, _ = self.c.constellation("orion", MIXED)
        self.write_directory(self.c.directory())
        self.cli("bob", "init", "--home", A)
        typo = A[:-1] + ("0" if A[-1] != "0" else "1")
        self.assertEqual(self.cli("bob", "address", "--home", typo, ok=False)["error"], "CliError")
