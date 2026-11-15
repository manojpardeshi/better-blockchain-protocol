"""A Byzantine witness or standby member answering malformed JSON must not crash honest clients.

docs/WIRE.md: "Nothing a witness sends is trusted." A reply of the wrong shape counts as no
answer (``Unreachable``, a ``Rejected``), so the wallet and the operator's tools carry on with the
other members. Found while extending the chaos harness to Byzantine standby members: a member
whose ``/v0/info`` answered ``{"ok": []}`` (or a reply without ``ok``, or a FREEZE / SUCCEED reply
that is not ``{sig, snapshot}``) raised ``TypeError``/``KeyError`` out of ``RemoteNetwork``, so
every payment in the home (``mirror_acks`` builds the committee clients) and every rotation crashed.
"""

import json
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from sigil.network import Network
from sigil.server import RemoteNetwork, RemoteStandby, RemoteWitness, Unreachable, WitnessServer, portable_snapshot
from sigil.wallet import Wallet
from sigil.witness import Rejected

GARBAGE = [b"{}", b"[]", b'{"ok": []}', b'{"ok": "x"}', b'{"ok": {"pk": 5}}', b'{"ok": {"pk": "aa", "stamps": 7}}',
           b'{"ok": {"pk": "aa", "constellation": null, "version": null, "stamps": {"n": "zz", "e": "3"}}}']


def garbage_server(reply: bytes, status: int = 200):
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def _send(self):
            n = int(self.headers.get("Content-Length", "0") or 0)
            if n:
                self.rfile.read(n)
            self.send_response(status)
            self.send_header("Content-Length", str(len(reply)))
            self.end_headers()
            self.wfile.write(reply)

        do_GET = do_POST = _send

    srv = ThreadingHTTPServer(("127.0.0.1", 0), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv, f"http://127.0.0.1:{srv.server_address[1]}"


class MalformedReplies(unittest.TestCase):
    def serve(self, reply: bytes, status: int = 200) -> str:
        srv, url = garbage_server(reply, status)
        self.addCleanup(srv.server_close)
        self.addCleanup(srv.shutdown)
        return url

    def test_clients_treat_malformed_replies_as_no_answer(self):
        for reply in GARBAGE:
            for status in (200, 403):
                with self.subTest(reply=reply, status=status):
                    url = self.serve(reply, status)
                    for cls in (RemoteWitness, RemoteStandby):
                        if cls is RemoteStandby and b'"stamps"' in reply:
                            continue  # a standby member's stamps are never read
                        with self.assertRaises(Rejected):
                            cls(url, 2)

    def test_calls_on_a_member_that_turns_byzantine(self):
        """The member answered ``info`` well, then garbage to every call."""
        good = json.dumps({"ok": {"pk": "ab" * 32, "constellation": None, "version": None, "stamps": None}}).encode()
        for reply in GARBAGE:
            with self.subTest(reply=reply):
                w = RemoteWitness(self.serve(good), 2)
                w.url = self.serve(reply)
                for call in (lambda: w.status("00" * 32), lambda: w.freeze({}), lambda: w.sell_stamp(5),
                             lambda: w.spend({})):
                    try:
                        call()
                    except Rejected:
                        pass
                s = RemoteStandby(self.serve(good), 2)
                s.url = w.url
                for call in (lambda: s.status("00" * 32), lambda: s.succeed({}), lambda: s.mirror_bind({})):
                    try:
                        call()
                    except Rejected:
                        pass

    def test_wallet_pays_with_a_byzantine_member_and_standby_member(self):
        """Three honest witnesses of four over HTTP, one serving garbage; a committee member that
        serves garbage too: the wallet still pays (f = 1)."""
        net = Network()
        X = net.create_constellation("orion", 4)
        servers = [WitnessServer(w).start() for w in net.all_witnesses(X)[:3]]
        for s in servers:
            self.addCleanup(s.stop)
        urls = [s.url for s in servers] + [self.serve(b'{"ok": []}')]
        rnet = RemoteNetwork({X: urls}, timeout=2, committees={X: [self.serve(b"[]")]})
        self.assertEqual(len(rnet.witnesses(X)), 3)
        self.assertEqual(rnet.committee(X), [])
        alice, bob = Wallet("alice", rnet, X), Wallet("bob", rnet, X)
        usd = alice.issue("USD", 10)
        alice.pay(bob, usd, 3)
        self.assertEqual(bob.balance(usd), 3)

    def test_byzantine_handover_reply_is_cleaned(self):
        """A FREEZE snapshot with unportable entries: only portable object entries are relayed."""
        snap = {"s1": [{"kind": "bind"}, 5, {"x": float("nan")}, {"x": 1 << 130}, {"x": "\ud800"}],
                "\ud800": [{"kind": "bind"}], "s2": "notalist", "s3": [{"x": [[[]]]}]}
        self.assertEqual(portable_snapshot(snap), {"s1": [{"kind": "bind"}], "s3": [{"x": [[[]]]}]})
        deep = {"s": [{"x": json.loads("[" * 300 + "]" * 300)}]}
        self.assertEqual(portable_snapshot(deep), {})
        w = RemoteWitness.__new__(RemoteWitness)   # the reply check, without a server
        w.url = "u"
        with self.assertRaises(Unreachable):
            w._sig_snapshot("freeze", {"sig": 5, "snapshot": {}})
        self.assertEqual(w._sig_snapshot("freeze", {"sig": "x", "snapshot": snap | {"s2": []}})[1],
                         {"s1": [{"kind": "bind"}], "s3": [{"x": [[[]]]}]})


if __name__ == "__main__":
    unittest.main()
