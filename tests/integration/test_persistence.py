"""Scenario 8: wallet persistence. Every CLI command runs as a fresh process on the wallet
directory, and a payment that failed during a witness outage is retried after it.

The CLI has no flag for the authorisation lifetime, so the tests shorten it in
``state.json`` (``pledge_ttl``, ``max_skew``: fields ``sigil/wallet_store.py``
persists) instead of waiting the default twelve minutes.
"""

import json
import os
import signal
import stat
import unittest

from sigil import model, wallet_store
from tests.integration.harness import MIXED, IntegrationCase, wait_until


class PersistenceTests(IntegrationCase):
    def setUp(self):
        super().setUp()
        self.A, self.a_idx = self.c.constellation("orion", MIXED, start=False)
        self.B, self.b_idx = self.c.constellation("lyra", ["python", "rust", "python", "rust"], start=False)
        self.c.start_all(self.a_idx + self.b_idx)
        self.write_directory(self.c.directory())

    def state(self, who: str) -> dict:
        with open(os.path.join(self.wpath(who), wallet_store.STATE)) as f:
            return json.load(f)

    def short_pledges(self, who: str, ttl: int = 3, skew: int = 1) -> None:
        path = os.path.join(self.wpath(who), wallet_store.STATE)
        st = self.state(who)
        st.update(pledge_ttl=ttl, max_skew=skew)
        with open(path, "w") as f:
            json.dump(st, f)

    def outage_and_retry(self) -> tuple[str, str, dict]:
        """alice's payment to carol fails while two of A's four witnesses are down; once they
        are back and the authorisation has expired, alice's next ``pay`` completes it.
        Returns (usd, the completed tid, the output of the retrying ``pay``)."""
        c, A = self.c, self.A
        usd = self.cli("alice", "issue", "USD", "500")["asset"]
        down = [i for i in self.a_idx if c.witnesses[i]["kind"] == "rust"][:1] + \
               [i for i in self.a_idx if c.witnesses[i]["kind"] == "python"][:1]
        for i in down:
            c.kill(i, signal.SIGKILL)
        err = self.cli("alice", "pay", self.address_file("carol"), usd, 50, "--out", self.file("lost.json"), ok=False)
        self.assertEqual(err["error"], "SealFailed")
        # The pledge and the transition were saved before any witness saw them.
        st = self.state("alice")
        (tid,) = st["pending"]
        (s, (g, t, expires)), = [(s, v) for s, v in st["pledged"].items() if v[1] == tid]
        self.assertEqual((g, t), (0, tid))
        self.assertEqual(self.cli_balance("alice", usd), 500)           # still held, pledged
        self.assertIn("insufficient funds", self.cli("alice", "pay", self.address_file("carol"), usd, 1,
                                                     "--out", self.file("x.json"), ok=False)["message"])
        bound = [w for w in self.net().witnesses(A) if w.status(s)["tid"] == tid]
        self.assertEqual(len(bound), 2)                                  # the two that were up
        for i in down:
            c.start(i)
        for i in down:
            c.wait_ready(i)
        wait_until(expires + st["max_skew"] + 1, "the failed authorisation to expire")
        out = self.cli("alice", "pay", self.address_file("carol"), usd, 20, "--out", self.file("pay-20.json"))
        # The retried payment is handed out: its payment file is written and listed, then cleared.
        self.assertEqual([c["tid"] for c in out["completed"]], [tid])
        self.assertEqual(self.state("alice")["completed"], [])
        self.assertEqual(out["balance"], 500 - 50 - 20)                 # the retried payment and the new one
        return usd, tid, out

    def test_every_command_across_restarts_and_retry_after_outage(self):
        A, B = self.A, self.B
        for who, home in (("alice", A), ("bob", B), ("carol", A)):
            self.cli(who, "init", "--home", home, "--name", who)
        self.short_pledges("alice")
        mode = stat.S_IMODE(os.stat(os.path.join(self.wpath("alice"), wallet_store.KEYS)).st_mode)
        self.assertEqual(mode, 0o600)
        # An address handed out by one process is honoured by a later one.
        bob_addr = self.address_file("bob")
        with open(bob_addr) as f:
            self.assertIn(model.sigil_of(json.load(f)), self.state("bob")["issued"])
        gold = self.cli("bob", "issue", "GOLD", "9", "--home", A)["asset"]   # bob's asset lives in A
        usd, done, _out = self.outage_and_retry()
        self.assertEqual(self.cli("carol", "receive", self.file("pay-20.json"))["received"][0]["amount"], 20)
        # The payment the retry completed was handed out as its own payment file.
        handed = next(c["out"] for c in _out["completed"] if c["tid"] == done)
        self.assertEqual(self.cli("carol", "receive", handed, "--deep")["received"][0]["amount"], 50)
        pay, r = self.cli_pay("alice", "bob", usd, 100)
        with open(pay) as f:
            self.assertEqual(json.load(f)["refs"], [model.ref(r["tid"], 0)])
        self.cli("bob", "receive", pay, "--deep")
        self.assertEqual(self.cli("bob", "receive", pay), {"already": True, "received": []})
        self.cli("bob", "pay", bob_addr, gold, 4, "--out", self.file("gold.json"))   # to an old address of his own
        # Paying oneself credits the parcel at once; receiving the file is then a no-op.
        self.assertEqual(self.cli("bob", "receive", self.file("gold.json")), {"already": True, "received": []})
        self.assertEqual(self.cli("alice", "balance"), {usd: 330})
        self.assertEqual(self.cli("bob", "balance"), {usd: 100, gold: 9})
        self.assertEqual(self.cli("carol", "assets"), [{"asset": usd, "name": "USD", "balance": 70}])
        self.assertEqual(self.cli("alice", "export-dossier")["transitions"].keys(),
                         self.load_wallet("alice").dossier.transitions.keys())
        self.check_invariants({w: self.load_wallet(w) for w in ("alice", "bob", "carol")})

    def test_cli_hands_out_a_payment_completed_by_a_retry(self):
        """BUG (CLI, medium: a payment is made but never delivered): when ``pay`` completes an
        earlier payment that had failed (``Wallet.release_expired_pledges`` -> ``_settle``), the
        CLI never tells the user and never writes that payment's file.

        Scenario: alice's ``pay`` to carol fails with SealFailed while two of four witnesses are
        down; two witnesses bound the payment. After they are back and the authorisation has
        expired, alice runs ``pay`` again (to anyone). Before selecting inputs, the wallet
        settles the old pledge: it re-authorises the same transition and seals it, so carol's
        payment is now final and alice's balance is lower by it. The tid goes to
        ``Wallet.completed`` ("hand their dossiers to the payees"), which ``wallet_store``
        persists, but no CLI command reads it: the earlier ``--out`` file was never written,
        the new ``pay`` output mentions only the new payment, and carol cannot ``receive``.
        The payee's parcel exists but is undeliverable unless the payer digs it out of
        ``export-dossier`` by hand.

        Suggested fix: when ``pay`` (or any command that settles pledges) completes a pending
        transition, write its payment file (e.g. next to ``--out`` or to a ``completed/``
        directory in the wallet) and list it in the JSON output; add a command that re-exports
        the payment file of a tid in ``completed`` (and clears it once handed over).
        """
        for who in ("alice", "carol"):
            self.cli(who, "init", "--home", self.A, "--name", who)
        self.short_pledges("alice")
        _usd, done, out = self.outage_and_retry()
        self.assertIn(done, json.dumps(out), "the retried pay reports the payment it completed")
