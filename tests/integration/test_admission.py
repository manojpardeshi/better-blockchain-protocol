"""Scenario 7: admission control on open (non-loopback) listeners, and paying with stamps.

Witnesses listen on 0.0.0.0, so the per-client rate limit is on by default
(docs/WIRE.md "Admission control"). Clients are told apart by address: an
abusive client is played from 127.0.0.2, the honest wallets from 127.0.0.1.
"""

import http.client
import json
import signal
import threading
import unittest
import urllib.parse

from sigil import model, wallet_store
from sigil.ratelimit import DEFAULT_BURST
from sigil.wallet import SealFailed, Wallet
from sigil.witness import Rejected
from tests.integration.harness import MIXED, IntegrationCase, bare_client, manual_spend, poll, wait_until

ATTACKER = "127.0.0.2"


def post_from(source: str, url: str, path: str, body: dict) -> tuple[int, dict, dict]:
    """POST from a chosen source address (a different client to the witness's rate limiter)."""
    u = urllib.parse.urlsplit(url)
    conn = http.client.HTTPConnection(u.hostname, u.port, timeout=10, source_address=(source, 0))
    try:
        conn.request("POST", path, body=json.dumps(body).encode(), headers={"Content-Type": "application/json"})
        r = conn.getresponse()
        return r.status, json.loads(r.read()), {k.lower(): v for k, v in r.getheaders()}
    finally:
        conn.close()


class AdmissionTests(IntegrationCase):
    def open_constellation(self, name: str, kinds: list, extra: dict | None = None) -> tuple[str, list]:
        cid, idx = self.c.constellation(name, kinds, extra=extra, start=False)
        for i in idx:
            self.c.witnesses[i]["listen"] = "0.0.0.0"
        self.c.start_all(idx)
        return cid, idx

    def test_open_listener_limits_each_client_separately(self):
        O, idx = self.open_constellation("open", MIXED)               # no --rate-limit: on by default
        urls = self.c.urls(idx)
        self.write_directory({O: urls})
        for who in ("alice", "bob"):
            self.cli(who, "init", "--home", O, "--name", who)
        usd = self.cli("alice", "issue", "USD", "100")["asset"]

        # An abusive client exhausts its bucket at every witness, Rust and Python alike.
        for url in urls:
            n = 0
            while True:
                code, body, headers = post_from(ATTACKER, url, "/v0/status", {"sigil": "00" * 32})
                if code == 429:
                    break
                self.assertEqual(code, 200, body)
                n += 1
                self.assertLess(n, DEFAULT_BURST + 200, "never rate limited")
            self.assertGreaterEqual(n, DEFAULT_BURST - 2)
            self.assertEqual(body, {"error": "rejected", "message": "rate limited", "vote": None})
            self.assertGreaterEqual(int(headers["retry-after"]), 1)
            # Operator calls are not rate limited: the admin token decides.
            code, body, _ = post_from(ATTACKER, url, "/v0/freeze", {})
            self.assertEqual((code, body["message"]), (403, "bad admin token"))

        # It keeps hammering while the honest wallets pay: they are not affected.
        stop, counts = threading.Event(), {200: 0, 429: 0}

        def hammer():
            while not stop.is_set():
                for url in urls:
                    code = post_from(ATTACKER, url, "/v0/status", {"sigil": "00" * 32})[0]
                    counts[code] = counts.get(code, 0) + 1

        t = threading.Thread(target=hammer, daemon=True)
        t.start()
        try:
            for amount in (10, 20, 30):
                pay, _ = self.cli_pay("alice", "bob", usd, amount)
                self.cli("bob", "receive", pay, "--deep")
        finally:
            stop.set()
            t.join(30)
        self.assertGreater(counts[429], 10 * counts[200], counts)
        self.assertEqual((self.cli_balance("alice", usd), self.cli_balance("bob", usd)), (40, 60))
        self.check_invariants({w: self.load_wallet(w) for w in ("alice", "bob")})

    def test_wallet_over_its_own_limit_fails_cleanly_and_recovers(self):
        T, idx = self.open_constellation("tight", MIXED, extra={"rust": ["--rate-limit", "5", "--rate-burst", "15"],
                                                                 "python": ["--rate-limit", "5", "--rate-burst", "15"]})
        net = self.net({T: self.c.urls(idx)})
        alice = Wallet("alice", net, T, pledge_ttl=2, max_skew=1)
        bob = Wallet("bob", net, T)
        usd = alice.issue("USD", 1000)
        paid = 0
        for _ in range(40):                           # far faster than 5 requests per second
            try:
                alice.pay(bob, usd, 1)
                paid += 1
            except SealFailed:
                break
        else:
            self.fail("the wallet was never rate limited")
        self.assertGreaterEqual(paid, 1)
        self.assertEqual(len(alice.pending), 1)      # the failed payment is a pledge, kept
        (tid,) = alice.pending
        expires = max(e for _g, t, e in alice.pledged.values() if t == tid)
        # Once the authorisation has expired (and the buckets refilled), the next payment first
        # settles the pledge: it completes the partly bound payment or drops an unbound one.
        wait_until(expires + alice.max_skew + 1, "the pledge to expire")
        for url in self.c.urls(idx):
            poll(lambda url=url: _answers(url), timeout=30, interval=0.2, what=f"{url} to admit us again")
        alice.pay(bob, usd, 1)
        paid += 1
        self.assertEqual(alice.pending, {})
        live = {h["sigil"] for h in alice.holdings.values()}
        self.assertFalse(live & set(alice.pledged), "no parcel left pledged")
        for done in alice.completed:                  # a completed retry is handed to the payee
            bob.receive(alice.dossier.ancestry([done]), [model.ref(done, 0)])
            paid += 1
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (1000 - paid, paid))
        self.check_invariants({"alice": alice, "bob": bob})

    def test_stamps(self):
        c = self.c
        S, idx = c.constellation("stamped", MIXED, extra={"rust": ["--stamps"], "python": ["--stamps"]})
        net = self.net({S: c.urls(idx)})
        adir = self.wpath("alice")
        alice = Wallet("alice", net, S, pledge_ttl=2, max_skew=1)
        bob = Wallet("bob", net, S)
        usd = alice.issue("USD", 100)
        # Without stamps no witness votes, and nothing is bound.
        with self.assertRaises(SealFailed):
            alice.pay(bob, usd, 10)
        (s, (_g, _tid, expires)), = alice.pledged.items()
        self.assertTrue(all(w.status(s)["tid"] is None for w in net.witnesses(S)))
        # alice buys two blind stamps from every witness; they survive a wallet restart.
        alice.buy_stamps(S, 2)
        wallet_store.save(alice, adir)
        alice = wallet_store.load(adir, self.net({S: c.urls(idx)}))
        self.assertEqual(sorted(len(v) for v in alice.stamps.values()), [2, 2, 2, 2])
        wait_until(expires + alice.max_skew + 1, "the stampless pledge to expire")
        alice.pay(bob, usd, 10)                       # frees the dead pledge, then pays
        self.assertEqual(sorted(len(v) for v in alice.stamps.values()), [1, 1, 1, 1])
        spare = {pk: list(v) for pk, v in alice.stamps.items()}
        # A Rust and a Python witness restart: stamps sold before stay valid (the key persists).
        for i in (idx[0], idx[1]):
            c.restart(i)
        alice.network = self.net({S: c.urls(idx)})
        alice.pay(bob, usd, 5)
        self.assertEqual(sum(len(v) for v in alice.stamps.values()), 0)
        # A redeemed stamp is refused, even after the restart.
        refs, _ = alice.select(usd, 1)
        a = bob.address()
        *_, reqs = manual_spend(alice, refs, [model.parcel(S, usd, 85, a["lock"], a["salt"])])
        for w in alice.network.witnesses(S):
            with self.assertRaises(Rejected) as e:
                w.spend(dict(reqs[0], stamp=spare[w.pk][0]))
            self.assertIn("stamp", str(e.exception))
            self.assertIsNone(w.status(reqs[0]["sigil"])["tid"])
        bob.buy_stamps(S, 1)
        bob.pay(alice, usd, 3)
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (88, 12))
        self.check_invariants({"alice": alice, "bob": bob})

    @unittest.expectedFailure
    def test_cli_wallet_pays_in_a_stamped_constellation(self):
        """BUG (CLI, medium: CLI unusable against stamp-requiring witnesses): the command-line
        wallet has no way to obtain stamps, so it can never pay when the home's witnesses run
        with ``--stamps`` (the deployment SPEC §5.6 recommends wherever stamps can be paid for).

        Scenario: S's witnesses (Rust and Python) require a stamp with every SPEND. ``Wallet``
        can buy them (``buy_stamps``) and ``wallet_store`` persists them, but ``sigil/cli.py``
        exposes no command for it, and ``pay`` does not buy any: every witness answers "missing
        or spent stamp", ``pay`` fails with SealFailed and the parcel stays pledged until the
        authorisation expires.

        Suggested fix: a ``buy-stamps CID COUNT`` command (``Wallet.buy_stamps`` + save), and/or
        have ``pay`` buy one stamp per witness that advertises a stamp key in ``/v0/info`` when
        the wallet holds none for it.
        """
        S, idx = self.c.constellation("stamped", MIXED, extra={"rust": ["--stamps"], "python": ["--stamps"]})
        self.write_directory({S: self.c.urls(idx)})
        for who in ("alice", "bob"):
            self.cli(who, "init", "--home", S, "--name", who)
        usd = self.cli("alice", "issue", "USD", "100")["asset"]
        self.cli("alice", "buy-stamps", S, "2")
        pay, _ = self.cli_pay("alice", "bob", usd, 10)
        self.cli("bob", "receive", pay)


def _answers(url: str) -> bool:
    try:
        bare_client(url).status("00" * 32)
        return True
    except Rejected:
        return False


if __name__ == "__main__":
    unittest.main()
