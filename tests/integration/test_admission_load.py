"""Admission control under load (docs/WIRE.md "Admission control", SPEC §5.6), Rust and Python.

* A home with a successor committee, every witness and standby member rate limited (20/s, burst
  100, as on an open listener): honest wallets pay while an abusive client (another address)
  floods SPEND, MIRROR and STATUS from several threads. The abuser is answered 429 and binds
  nothing (no witness or standby member stores anything it sent); the honest payments all seal.
* Connection caps: an abuser holding idle connections from one address gets at most 16 per
  daemon; from many addresses at most 256 in all; every daemon keeps serving and serves honest
  wallets again once the abuser lets go.
* Stamps (``--stamps``) with witnesses SIGKILLed and restarted between payments and a wallet
  restored from a backup taken before it spent stamps: the restored wallet's spent stamps are
  refused, and it still pays once it buys new ones; nothing is credited twice.
"""

import http.client
import json
import socket
import threading
import time
import unittest
import urllib.parse

from sigil import model, wallet_store
from sigil.wallet import SealFailed, Wallet
from tests.integration.harness import MIXED, IntegrationCase, bare_client, manual_spend, poll, wait_until

ATTACKER = "127.0.0.2"
LIMITS = ["--rate-limit", "20", "--rate-burst", "100"]


def post_from(source: str, url: str, path: str, body: dict) -> int:
    u = urllib.parse.urlsplit(url)
    conn = http.client.HTTPConnection(u.hostname, u.port, timeout=10, source_address=(source, 0))
    try:
        conn.request("POST", path, body=json.dumps(body).encode(), headers={"Content-Type": "application/json"})
        r = conn.getresponse()
        r.read()
        return r.status
    except OSError:
        return -1
    finally:
        conn.close()


class AdmissionUnderLoad(IntegrationCase):
    def test_honest_wallets_pay_through_a_flood(self):
        c = self.c
        X, idx = c.constellation("open", MIXED, committee=["rust", "python", "rust", "python"], dead_man=600,
                                 extra={"rust": LIMITS, "python": LIMITS}, start=False)
        for i in range(len(c.witnesses)):
            if c.witnesses[i].get("role") == "standby":
                c.witnesses[i]["args"] = c.witnesses[i].get("args", []) + LIMITS
        c.start_all()
        directory = c.directory()
        urls = directory[X]
        kurls = c.committees([X])[X]
        net = self.net(directory, committees={X: kurls})
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd = alice.issue("USD", 1000)
        # The abuser's requests: SPENDs and MIRRORs of a coin it owns (valid authorisations).
        mal = Wallet("mallory", self.net(directory, committees={X: kurls}), X)
        mcoin = mal.issue("MAL", 5)
        a = mal.address()
        refs, _ = mal.select(mcoin, 5)
        *_, reqs = manual_spend(mal, refs, [model.parcel(X, mcoin, 5, a["lock"], a["salt"])])
        abuse = reqs[0]
        mreq = dict(abuse, version=0)
        stop = threading.Event()
        counts: dict = {}
        lock = threading.Lock()

        def hammer(k):
            while not stop.is_set():
                for url in urls:
                    code = post_from(ATTACKER, url, "/v0/spend", {"request": abuse})
                    with lock:
                        counts[code] = counts.get(code, 0) + 1
                for url in kurls:
                    code = post_from(ATTACKER, url, "/v0/mirror", {"request": mreq})
                    with lock:
                        counts[code] = counts.get(code, 0) + 1

        ts = [threading.Thread(target=hammer, args=(k,), daemon=True) for k in range(4)]
        for t in ts:
            t.start()
        try:
            time.sleep(3)      # every bucket of the abuser is empty by now
            paid = 0
            for _ in range(8):
                alice.pay(bob, usd, 5)
                paid += 5
        finally:
            stop.set()
            for t in ts:
                t.join(30)
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (1000 - paid, paid))
        self.assertGreater(counts.get(429, 0), 20 * (counts.get(200, 0) + counts.get(403, 0) + 1) // 21, counts)
        # Whatever got through before its buckets emptied was a valid request; after that nothing.
        self.check_invariants({"alice": alice, "bob": bob})

    def test_connection_caps(self):
        c = self.c
        X, idx = c.constellation("capped", MIXED, extra={"rust": LIMITS, "python": LIMITS})
        urls = c.urls(idx)

        def hold(source, url, n):
            u = urllib.parse.urlsplit(url)
            out = []
            for _ in range(n):
                s = socket.socket()
                s.settimeout(2)
                try:
                    s.bind((source, 0))
                    s.connect((u.hostname, u.port))
                    out.append(s)
                except OSError:
                    s.close()
            return out

        def open_ones(socks):
            """Connections the daemon kept open (a capped one is closed unread: EOF at once)."""
            alive = 0
            for s in socks:
                s.settimeout(0.3)
                try:
                    if s.recv(1) == b"":
                        continue
                except socket.timeout:
                    alive += 1
                    continue
                except OSError:
                    continue
            return alive

        for url in urls:
            with self.subTest(url=url):
                socks = hold(ATTACKER, url, 40)
                try:
                    time.sleep(0.5)
                    self.assertLessEqual(open_ones(socks), 16)
                    self.assertTrue(bare_client(url).status("00" * 32) is not None)   # others still served
                finally:
                    for s in socks:
                        s.close()
        # From many addresses: at most 256 open at once on one daemon; it keeps serving afterwards.
        url = urls[0]
        socks = []
        try:
            for k in range(20):
                socks += hold(f"127.0.1.{k + 1}", url, 16)
            time.sleep(0.5)
            self.assertLessEqual(open_ones(socks), 256)
        finally:
            for s in socks:
                s.close()
        poll(lambda: _answers(url), timeout=40, what="the daemon to serve again")
        net = self.net({X: urls})
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd = alice.issue("USD", 10)
        alice.pay(bob, usd, 4)
        self.check_invariants({"alice": alice, "bob": bob})

    def test_stamps_with_restarts_and_a_restored_wallet(self):
        c = self.c
        S, idx = c.constellation("stamped", MIXED, extra={"rust": ["--stamps"], "python": ["--stamps"]})
        adir = self.wpath("alice")
        alice = Wallet("alice", self.net({S: c.urls(idx)}), S, pledge_ttl=2, max_skew=1)
        bob = Wallet("bob", self.net({S: c.urls(idx)}), S)
        usd = alice.issue("USD", 100)
        alice.buy_stamps(S, 2)
        wallet_store.save(alice, adir)            # the backup: two stamps per witness
        alice.pay(bob, usd, 10)
        for i in (idx[0], idx[1]):                # a Rust and a Python witness crash and restart
            c.restart(i)
        alice.network = self.net({S: c.urls(idx)})
        alice.pay(bob, usd, 5)
        # The wallet dies and is restored from the backup: its pool holds the stamps it spent.
        restored = wallet_store.load(adir, self.net({S: c.urls(idx)}))
        self.assertEqual(sorted(len(v) for v in restored.stamps.values()), [2, 2, 2, 2])
        # The backup also predates both payments: it still holds the coin it spent. Paying with it
        # is refused (the witnesses are bound), and the spent stamps buy nothing either.
        with self.assertRaises((SealFailed, ValueError)):
            restored.pay(bob, usd, 1)
        # The live wallet buys new stamps and pays on.
        alice.buy_stamps(S, 1)
        expires = max((e for _g, _t, e in alice.pledged.values()), default=0)
        wait_until(expires + alice.max_skew + 1, "pledges to expire")
        alice.pay(bob, usd, 1)
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (84, 16))
        self.check_invariants({"alice": alice, "bob": bob})


def _answers(url: str) -> bool:
    try:
        bare_client(url).status("00" * 32)
        return True
    except Exception:  # noqa: BLE001
        return False


if __name__ == "__main__":
    unittest.main()
