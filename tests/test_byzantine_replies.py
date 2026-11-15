"""Clients never crash on a malformed or Byzantine reply (docs/WIRE.md "Nothing a witness sends is trusted").

A ``JunkProxy`` stands in front of an honest witness or standby server: requests to the paths
it is told to spoil get a junk reply (wrong types, missing keys, non-object votes, non-JSON,
deep nesting, an 8 MiB body, malformed error replies), everything else is forwarded. Every
client call must either return a well-formed result or raise ``Rejected`` (``Unreachable``
for a malformed reply), never ``TypeError``/``KeyError``/``AttributeError``/``ValueError``/
``RecursionError``; and one such witness or standby member within f must not stop wallets,
rotations, successions or a standby member's probes.
"""

import json
import threading
import time
import unittest
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from sigil import Network, Wallet, model
from sigil.charter import Registry, charter_body, charter_hash
from sigil.crypto import KeyPair
from sigil.gossip import GossipStore, gossip_round
from sigil.server import (RemoteNetwork, RemoteStandby, RemoteWitness, RotationIncomplete, StandbyServer,
                          Unreachable, WitnessServer)
from sigil.witness import Rejected, Witness

TOKEN = "t0ken"
DEAD = 3600
DEEP = 20000  # nesting far beyond Python's recursion limit


def _j(obj) -> bytes:
    return json.dumps(obj).encode()


WRONG = {"gen": "zero", "tid": 7, "votes": "none", "pk": 5, "constellation": [1], "version": "v",
         "frozen": "no", "stamps": {"n": "zz", "e": 1}, "sig": 3, "snapshot": 2, "answered": "many",
         "member": 1, "bindings": "none", "dead": "yes", "proofs": 1, "forks": 2, "charters": 3}

JUNK = {
    "not json": (200, b"{not json"),
    "empty body": (200, b""),
    "no ok": (200, b"{}"),
    "top-level list": (200, b"[1, 2]"),
    "ok string": (200, _j({"ok": "x"})),
    "ok list": (200, _j({"ok": [1, 2, 3]})),
    "ok null": (200, _j({"ok": None})),
    "ok float": (200, _j({"ok": 7.5})),
    "ok bool": (200, _j({"ok": True})),
    "wrong types": (200, _j({"ok": WRONG})),
    "missing keys": (200, _j({"ok": {"x": 1}})),
    "non-object items": (200, _j({"ok": {"gen": 0, "tid": None, "votes": [0, None, "x", {"gen": 0}],
                                          "bindings": [1, [0], ["a", 1], [0, 1, 2]],
                                          "charters": {"ab": 5, "cd": [1]}, "proofs": [1], "forks": [2]}})),
    "info-like, bad stamps": (200, _j({"ok": {"pk": "ab" * 32, "constellation": None, "version": None,
                                               "frozen": False, "stamps": {"n": "zz", "e": "3"}}})),
    "info-like, zero stamp key": (200, _j({"ok": {"pk": "ab" * 32, "constellation": "cd" * 32, "version": 0,
                                                   "frozen": False, "stamps": {"n": "0", "e": "0"}}})),
    "signed-looking, odd version": (200, _j({"ok": {"sig": "00", "snapshot": [], "constellation": "x",
                                                     "version": [1], "answered": -1}})),
    "deep nesting": (200, b'{"ok": ' + b"[" * DEEP + b"]" * DEEP + b"}"),
    "8 MiB": (200, _j({"ok": {"pad": "A" * (8 << 20)}})),
    "conflict, vote a list": (409, _j({"error": "conflict", "message": "x", "vote": [1, 2]})),
    "conflict, wrong-typed vote": (409, _j({"error": "conflict", "message": "x", "vote": {"gen": "x"}})),
    "error not an object": (403, b"[1]"),
    "error message not a string": (403, _j({"error": "rejected", "message": {"a": 1}, "vote": None})),
    "error deep nesting": (400, b"[" * DEEP + b"]" * DEEP),
    "500 binary": (500, b"\x00\xff garbage"),
}


class JunkProxy:
    """An HTTP front for an honest server that spoils the replies of chosen paths.

    ``junk`` maps a path (``status``, ``info``, ...; ``*`` for all) to ``(code, body)`` or to a
    callable taking the request handler (for replies that stream or stall).
    """

    def __init__(self, backend: str):
        self.backend = backend
        self.junk: dict = {}
        proxy = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"

            def log_message(self, *args):
                pass

            def _handle(self, method: str):
                path = self.path.removeprefix("/v0/")
                n = int(self.headers.get("Content-Length") or 0)
                data = self.body = self.rfile.read(n) if n else None
                spoil = proxy.junk.get(path, proxy.junk.get("*"))
                if callable(spoil):
                    return spoil(self)
                if spoil is not None:
                    return self.send(*spoil)
                headers = {k: v for k, v in self.headers.items() if k.lower() in ("content-type", "authorization")}
                req = urllib.request.Request(proxy.backend + self.path, data=data, method=method, headers=headers)
                try:
                    with urllib.request.urlopen(req, timeout=30) as r:
                        self.send(r.status, r.read())
                except urllib.error.HTTPError as e:
                    self.send(e.code, e.read())

            def send(self, code: int, data: bytes):
                try:
                    self.send_response(code)
                    self.send_header("Content-Type", "application/json")
                    self.send_header("Content-Length", str(len(data)))
                    self.end_headers()
                    self.wfile.write(data)
                except OSError:
                    pass

            def do_GET(self):
                self._handle("GET")

            def do_POST(self):
                self._handle("POST")

        class Server(ThreadingHTTPServer):
            daemon_threads = True

        self.httpd = Server(("127.0.0.1", 0), Handler)
        threading.Thread(target=self.httpd.serve_forever, daemon=True).start()

    @property
    def url(self) -> str:
        return f"http://127.0.0.1:{self.httpd.server_address[1]}"

    def stop(self):
        self.httpd.shutdown()
        self.httpd.server_close()


# What a well-formed result of each call looks like (anything else must raise ``Rejected``).

def _is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def _vote(v):
    return (isinstance(v, dict) and all(_is_int(v.get(k)) for k in ("gen", "version", "time"))
            and all(isinstance(v.get(k), str) for k in ("constellation", "witness", "sigil", "tid", "sig")))


def _status(st):
    return (isinstance(st, dict) and _is_int(st.get("gen")) and (st.get("tid") is None or isinstance(st["tid"], str))
            and isinstance(st.get("votes"), list) and all(_vote(v) for v in st["votes"]))


def _counts(x):
    return isinstance(x, dict) and all(_is_int(v) for v in x.values())


def _sig_snapshot(x):
    return isinstance(x, tuple) and len(x) == 2 and isinstance(x[0], str)


def _charters(x):
    return isinstance(x, dict) and all(isinstance(c, list) for c in x.values())


def _proofs(x):
    return isinstance(x, dict) and isinstance(x.get("proofs"), list) and isinstance(x.get("forks"), list)


WITNESS_CALLS = {
    "spend": ("spend", lambda c: c.spend({"sigil": "ab" * 32}), _vote),
    "release": ("release", lambda c: c.release("ab" * 32, {}), _is_int),
    "status": ("status", lambda c: c.status("ab" * 32), _status),
    "heartbeat": ("heartbeat", lambda c: c.heartbeat("ch"), lambda h: isinstance(h, dict)),
    "sell_stamp": ("sell_stamp", lambda c: c.sell_stamp(5), _is_int),
    "charters": ("charters", lambda c: c.charters(), _charters),
    "proofs": ("proofs", lambda c: c.proofs(), _proofs),
    "pull (proofs)": ("proofs", lambda c: c.pull(), lambda x: _proofs(x) and _charters(x.get("charters"))),
    "pull (charters)": ("charters", lambda c: c.pull(), lambda x: _proofs(x) and _charters(x.get("charters"))),
    "gossip": ("gossip", lambda c: c.gossip({}), _counts),
    "freeze": ("freeze", lambda c: c.freeze({"x": 1}), _sig_snapshot),
    "adopt": ("adopt", lambda c: (c.adopt("ab" * 32, 1, []), c)[1], lambda c: _member(c)),
}

STANDBY_CALLS = {
    "mirror": ("mirror", lambda c: c.mirror_bind({"sigil": "ab"}), lambda a: isinstance(a, dict)),
    "note_release": ("note_release", lambda c: c.note_release("ab", {}), lambda r: isinstance(r, bool)),
    "status": ("status", lambda c: c.status("ab"),
               lambda st: isinstance(st, dict) and isinstance(st.get("bindings"), list)),
    "info": ("info", lambda c: c.info(), lambda i: isinstance(i, dict) and isinstance(i.get("pk"), str)),
    "succeed": ("succeed", lambda c: c.succeed({"x": 1}), _sig_snapshot),
    "probe": ("probe", lambda c: c.probe([]), lambda n: _is_int(n) and n >= 0),
    "standby": ("standby", lambda c: (c.enter("ab" * 32, 1, []), c)[1], lambda c: _member(c)),
}


def _member(c):
    return isinstance(c.cid, str) and _is_int(c.version)


class ClientCalls(unittest.TestCase):
    """Every client call against every kind of junk reply: a well-formed result or ``Rejected``."""

    @classmethod
    def setUpClass(cls):
        cls.sim = Network()
        cls.X = cls.sim.create_constellation("orion", stamps=True,
                                             successor={"n": 4, "dead_man": DEAD})
        cls.wsrv = WitnessServer(cls.sim.all_witnesses(cls.X)[0], admin_token=TOKEN).start()
        cls.ssrv = StandbyServer(cls.sim.committees[cls.X][0], admin_token=TOKEN).start()
        cls.wproxy, cls.sproxy = JunkProxy(cls.wsrv.url), JunkProxy(cls.ssrv.url)

    @classmethod
    def tearDownClass(cls):
        for s in (cls.wproxy, cls.sproxy, cls.wsrv, cls.ssrv):
            s.stop()

    def _matrix(self, proxy, make, calls):
        bad = []
        for name, (path, call, valid) in calls.items():
            for kind, reply in JUNK.items():
                proxy.junk = {}
                client = make(proxy.url)
                proxy.junk = {path: reply}
                try:
                    out = call(client)
                except Rejected:
                    continue
                except Exception as e:  # noqa: BLE001 - what this test is about
                    bad.append(f"{name} / {kind}: {type(e).__name__}: {str(e)[:60]}")
                    continue
                if not valid(out):
                    bad.append(f"{name} / {kind}: returned {str(out)[:60]!r}")
        proxy.junk = {}
        return bad

    def test_witness_calls(self):
        bad = self._matrix(self.wproxy, lambda u: RemoteWitness(u, 5, admin_token=TOKEN), WITNESS_CALLS)
        self.assertEqual(bad, [], f"{len(bad)} junk replies crashed or fooled the client")

    def test_standby_calls(self):
        bad = self._matrix(self.sproxy, lambda u: RemoteStandby(u, 5, admin_token=TOKEN), STANDBY_CALLS)
        self.assertEqual(bad, [], f"{len(bad)} junk replies crashed or fooled the client")

    def test_info_at_construction(self):
        bad = []
        for cls in (RemoteWitness, RemoteStandby):
            for kind, reply in JUNK.items():
                for proxy in (self.wproxy, self.sproxy):
                    proxy.junk = {"info": reply}
                    try:
                        c = cls(proxy.url, 5)
                    except Rejected:
                        continue
                    except Exception as e:  # noqa: BLE001
                        bad.append(f"{cls.__name__} / {kind}: {type(e).__name__}: {str(e)[:60]}")
                        continue
                    if not (isinstance(c.pk, str) and (c.cid is None or isinstance(c.cid, str))
                            and (c.version is None or _is_int(c.version))):
                        bad.append(f"{cls.__name__} / {kind}: accepted {c.pk!r} {c.cid!r} {c.version!r}")
        self.wproxy.junk = self.sproxy.junk = {}
        self.assertEqual(bad, [], f"{len(bad)} junk INFO replies crashed or fooled the client")

    def test_honest_replies_pass_through(self):
        c = RemoteWitness(self.wproxy.url, 5)
        self.assertEqual(c.pk, self.sim.all_witnesses(self.X)[0].pk)
        self.assertIsNotNone(c.stamps)
        self.assertEqual(c.status("ab" * 32), {"gen": 0, "tid": None, "votes": []})
        self.assertIn(self.X, c.charters())
        self.assertEqual(RemoteStandby(self.sproxy.url, 5).status("ab"), {"bindings": []})


class Streams(unittest.TestCase):
    """Replies that never end, or trickle: the client stops reading (size cap, total deadline)."""

    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.srv = WitnessServer(self.sim.all_witnesses(self.X)[0]).start()
        self.proxy = JunkProxy(self.srv.url)
        self.addCleanup(self.srv.stop)
        self.addCleanup(self.proxy.stop)

    def _held(self, junk: dict, call, limit: float = 15.0) -> float:
        """Run ``call`` against the spoiled proxy; assert it ends in ``Unreachable`` within ``limit``."""
        self.proxy.junk = junk
        done = []

        def run():
            try:
                call()
            except Rejected as e:
                done.append(e)

        t0 = time.monotonic()
        t = threading.Thread(target=run, daemon=True)
        t.start()
        t.join(limit)
        self.assertFalse(t.is_alive(), f"the client was still reading after {limit} s")
        self.assertIsInstance(done[0], Unreachable)
        return time.monotonic() - t0

    def test_trickled_status_line_and_headers_hit_the_deadline(self):
        """Before: the deadline covered the body only; a status line and headers sent one byte
        every 0.3 s (inside the 0.5 s socket timeout) held ``RemoteWitness(url, 0.5)`` forever."""
        stop = threading.Event()
        self.addCleanup(stop.set)

        def trickle(h):
            try:
                for b in b"HTTP/1.1 200 OK\r\nX-Pad: " + b"a" * 10_000:
                    if stop.wait(0.3):
                        return
                    h.wfile.write(bytes([b]))
                    h.wfile.flush()
            except OSError:
                pass

        self.assertLess(self._held({"info": trickle}, lambda: RemoteWitness(self.proxy.url, 0.5)), 6)

    def test_endless_continue_lines_hit_the_deadline(self):
        """Before: ``http.client`` skips ``100 Continue`` responses in a loop, so a witness sending
        them forever held the client however short its timeout (Python 3.13 gives up after 100
        of them: 30 s at one every 0.3 s)."""
        stop = threading.Event()
        self.addCleanup(stop.set)

        def flood(h):
            try:
                while not stop.wait(0.3):
                    h.wfile.write(b"HTTP/1.1 100 Continue\r\n\r\n")
                    h.wfile.flush()
            except OSError:
                pass

        c = RemoteWitness(self.proxy.url, 0.5)
        self.assertLess(self._held({"status": flood}, lambda: c.status("ab")), 6)

    def test_redirect_is_not_followed(self):
        def redirect(h):
            h.send_response(302)
            h.send_header("Location", self.srv.url + h.path)
            h.send_header("Content-Length", "0")
            h.end_headers()

        self.proxy.junk = {"info": redirect}
        with self.assertRaises(Unreachable):
            RemoteWitness(self.proxy.url, 2)
        c = RemoteWitness(self.srv.url, 2)
        c.url = self.proxy.url
        self.proxy.junk = {"status": redirect}
        with self.assertRaises(Rejected):
            c.status("ab")

    def test_rate_limited_info_is_unreachable_and_the_member_absent(self):
        self.proxy.junk = {"info": (429, _j({"error": "rejected", "message": "rate limited", "vote": None}))}
        with self.assertRaises(Unreachable):
            RemoteWitness(self.proxy.url, 2)
        net = RemoteNetwork({self.X: [self.proxy.url]}, timeout=2, registry=self.sim.registry)
        self.assertEqual(net.witnesses(self.X), [])

    def test_replies_near_the_cap(self):
        from sigil.server import MAX_REPLY
        c = RemoteWitness(self.proxy.url, 5)
        for size, ok in ((MAX_REPLY - 64, True), (MAX_REPLY + 1, False)):
            body = _j({"ok": {"gen": 0, "tid": None, "votes": [], "pad": ""}})
            body = body.replace(b'"pad": ""', b'"pad": "' + b"x" * (size - len(body)) + b'"')
            self.assertEqual(len(body), size)
            self.proxy.junk = {"status": (200, body)}
            if ok:
                self.assertEqual(c.status("ab")["gen"], 0)
            else:
                with self.assertRaises(Unreachable):
                    c.status("ab")

    def test_empty_containers_stay_within_the_cap(self):
        """A full ordinary reply of ``[[],[],...]`` is cheap: the 256 KiB cap bounds it (a few MiB
        parsed), and none of it counts as a vote."""
        c = RemoteWitness(self.proxy.url, 5)
        body = b'{"ok": {"gen": 0, "tid": null, "votes": [' + b"[]," * 80_000 + b"[]]}}"
        self.proxy.junk = {"status": (200, body)}
        t0 = time.monotonic()
        self.assertEqual(c.status("ab")["votes"], [])
        self.assertLess(time.monotonic() - t0, 2)

    def test_escaped_quotes_parse_in_linear_time(self):
        """Before: a pre-filter regex over JSON strings was quadratic on a body of repeated ``\\"``
        (64 KiB took ~22 s, holding the GIL after the watchdog was cancelled)."""
        c = RemoteWitness(self.proxy.url, 5)
        quotes = b'\\"' * (120 << 10)
        for body in (b'{"ok": "' + quotes + b'"}', b'{"ok": "' + quotes):  # unterminated: the slow case
            self.proxy.junk = {"status": (200, body)}
            t0 = time.monotonic()
            with self.assertRaises(Unreachable):
                c.status("ab")
            self.assertLess(time.monotonic() - t0, 1)

    def test_pull_asks_chain_by_chain_only_when_the_charters_are_too_large(self):
        """Before: any failure of ``/v0/charters`` (an error, junk) sent one request per chain."""
        asked = []

        def chain(h):
            asked.append(h.path)
            h.send(200, _j({"ok": []}))

        c = RemoteWitness(self.proxy.url, 5)
        cids = ["ab" * 32, "cd" * 32]
        for junk in ((500, b"x"), (200, b"{not json")):
            self.proxy.junk = {"charters": junk, f"charters/{cids[0]}": chain, f"charters/{cids[1]}": chain}
            with self.assertRaises(Unreachable):
                c.pull(cids)
        self.assertEqual(asked, [])
        from sigil.server import MAX_RESPONSE
        self.proxy.junk = {"charters": (200, b'{"ok": {"x": "' + b"a" * MAX_RESPONSE + b'"}}'),
                           f"charters/{cids[0]}": chain, f"charters/{cids[1]}": chain}
        self.assertEqual(c.pull(cids)["charters"], {})
        self.assertEqual(sorted(asked), [f"/v0/charters/{x}" for x in cids])

    def test_charter_paths(self):
        """``/v0/charters/<cid>`` takes one path segment, as the Rust witness's route does."""
        import urllib.error
        import urllib.request

        def get(path):
            try:
                with urllib.request.urlopen(self.srv.url + path, timeout=5) as r:
                    return r.status, json.loads(r.read())
            except urllib.error.HTTPError as e:
                return e.code, json.loads(e.read())

        self.assertEqual(get(f"/v0/charters/{self.X}")[1]["ok"], self.sim.registry.chain(self.X))
        self.assertEqual(get(f"/v0/charters/{self.X}?x=1")[1]["ok"], self.sim.registry.chain(self.X))
        self.assertEqual(get("/v0/charters/" + "ab" * 32), (200, {"ok": []}))
        for bad in ("/v0/charters/", "/v0/charters/a/b", f"/v0/charters/{self.X}/"):
            self.assertEqual(get(bad), (404, {"error": "bad_request", "message": "unknown path", "vote": None}), bad)

    def test_dense_snapshots_are_accepted(self):
        """Before: FREEZE replies with many small containers were refused, and a snapshot carries
        every binding's header verbatim (a witness accepts extra header fields up to 32 KiB), so
        anyone could make every member's FREEZE reply refused after the members froze for good."""
        c = RemoteWitness(self.srv.url, 5, admin_token="t")
        c.url = self.proxy.url
        pad = [[]] * 10_000
        snapshot = {f"{i:02d}" * 32: [{"kind": "bind", "header": {"inputs": [], "body": "00", "pad": pad}}]
                    for i in range(3)}
        self.proxy.junk = {"freeze": (200, _j({"ok": {"sig": "ab", "snapshot": snapshot}}))}
        self.assertEqual(c.freeze({"x": 1}), ("ab", snapshot))

    def test_endless_reply_is_cut_off(self):
        """Before: ``_call`` read the whole body however large (only gossip pulls were capped)."""
        sent = []

        def endless(h):
            n = 0
            try:
                h.send_response(200)
                h.send_header("Content-Type", "application/json")
                h.end_headers()
                h.wfile.write(b'{"ok": "')
                chunk = b"A" * (1 << 20)
                while n < (96 << 20):
                    h.wfile.write(chunk)
                    n += len(chunk)
            except OSError:
                pass
            sent.append(n)

        c = RemoteWitness(self.proxy.url, 5)
        for path, call in (("status", lambda: c.status("ab")), ("info", lambda: RemoteWitness(self.proxy.url, 5)),
                           ("charters", c.charters)):
            sent.clear()
            self.proxy.junk = {path: endless}
            with self.assertRaises(Unreachable):
                call()
            for _ in range(100):
                if sent:
                    break
                time.sleep(0.05)
            self.assertTrue(sent and sent[0] < (64 << 20), f"{path}: the client read {sent} bytes")

    def test_trickling_reply_hits_a_deadline(self):
        """Before: a reply sending one byte just inside the socket timeout held the client forever."""
        stop = threading.Event()
        self.addCleanup(stop.set)

        def trickle(h):
            try:
                h.send_response(200)
                h.end_headers()
                while not stop.wait(0.1):
                    h.wfile.write(b" ")
                    h.wfile.flush()
            except OSError:
                pass

        c = RemoteWitness(self.proxy.url, 0.5)
        self.proxy.junk = {"status": trickle}
        done = []

        def run():
            try:
                c.status("ab")
            except Rejected as e:
                done.append(e)

        t0 = time.monotonic()
        t = threading.Thread(target=run, daemon=True)
        t.start()
        t.join(15)
        self.assertFalse(t.is_alive(), "the client was still reading after 15 s")
        self.assertIsInstance(done[0], Unreachable)
        self.assertLess(time.monotonic() - t0, 15)


class OneJunkWitness(unittest.TestCase):
    """One witness of four (f = 1) answers junk: wallets still pay, receive, settle and gossip."""

    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.servers = [WitnessServer(w, admin_token=TOKEN).start() for w in self.sim.all_witnesses(self.X)]
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        self.proxy = JunkProxy(self.servers[0].url)
        self.addCleanup(self.proxy.stop)
        self.urls = [self.proxy.url] + [s.url for s in self.servers[1:]]

    def _flow(self, junk: dict):
        self.proxy.junk = junk
        net = RemoteNetwork({self.X: self.urls}, timeout=5)
        clock = self.sim.clock
        alice = Wallet("alice", net, self.X, deep_threshold=1, clock=clock)
        bob = Wallet("bob", net, self.X, deep_threshold=1, clock=clock)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 40)                     # SPEND, STATUS (receive), deep confirmation
        bob.pay(alice, usd, 10)
        # A pledge that never reached a witness, settled after expiry: rule 3 cannot drop it
        # (the junk member does not answer), so it is completed instead.
        a = bob.address()
        refs, outputs = alice.payment_outputs(usd, 5, a)
        header, body, tid = alice.prepare(refs, outputs)
        alice.authorise(header, body)
        clock.advance(alice.pledge_ttl + alice.max_skew + 1)
        alice.release_expired_pledges()
        self.assertNotIn(tid, alice.pending)
        # completed, or dropped as provably unbound (rule 3): either way the coin is free again
        self.assertTrue(tid in alice.dossier.transitions or all(p[1] != tid for p in alice.pledged.values()))
        gossip_round(net, GossipStore(Registry()))
        self.assertEqual(net.find_votes("ab" * 32), [])
        net.refresh_charters(self.X)
        self.assertIn(self.X, net.registry)

    def test_every_path_junk(self):
        for kind, reply in JUNK.items():
            with self.subTest(kind):
                self._flow({"*": reply})

    def test_every_path_but_info_junk(self):
        for kind, reply in JUNK.items():
            with self.subTest(kind):
                self._flow({p: reply for p in ("spend", "status", "release", "charters", "proofs", "gossip",
                                               "heartbeat")})

    def test_a_signed_vote_with_odd_field_types(self):
        """A Byzantine member signs votes with its real key, whatever fields it likes: a vote whose
        ``version`` is a list or a string must count as no vote (before: ``request_seal`` grouped
        votes by an unhashable or unsortable version and raised ``TypeError``)."""
        kp = self.sim.all_witnesses(self.X)[0].kp

        def odd_vote(version):
            def reply(h):
                req = json.loads(h.body)["request"]
                g = next(g for s, g in req["header"]["inputs"] if s == req["sigil"])
                v = {"constellation": self.X, "version": version, "witness": kp.pk, "sigil": req["sigil"],
                     "gen": g, "tid": model.transition_id(req["header"]), "time": 1}
                v["sig"] = kp.sign("vote", model.vote_payload(v))
                h.send(200, _j({"ok": v}))
            return reply

        for version in ([0], "0", None, 0.0, {"v": 0}):
            with self.subTest(version=version):
                self.proxy.junk = {"spend": odd_vote(version)}
                net = RemoteNetwork({self.X: self.urls}, timeout=5)
                alice = Wallet("alice", net, self.X, clock=self.sim.clock)
                bob = Wallet("bob", net, self.X, clock=self.sim.clock)
                usd = alice.issue("USD", 100)
                alice.pay(bob, usd, 40)
                self.assertEqual(bob.balance(usd), 40)

    def test_stamps_from_a_junk_seller(self):
        Y = self.sim.create_constellation("lyra", stamps=True)
        servers = [WitnessServer(w).start() for w in self.sim.all_witnesses(Y)]
        self.addCleanup(lambda: [s.stop() for s in servers])
        proxy = JunkProxy(servers[0].url)
        self.addCleanup(proxy.stop)
        net = RemoteNetwork({Y: [proxy.url] + [s.url for s in servers[1:]]}, timeout=5)
        honest = [w.pk for w in self.sim.all_witnesses(Y)[1:]]
        junk = dict(JUNK, **{"valid hex, wrong signature": (200, _j({"ok": "1234abcd"}))})
        for kind, reply in junk.items():
            with self.subTest(kind):
                alice = Wallet("alice", net, Y)
                proxy.junk = {"sell_stamp": reply}
                alice.buy_stamps(Y, 2)   # before: one bad seller raised and stopped the loop
                self.assertEqual({pk: len(alice.stamps[pk]) for pk in honest}, dict.fromkeys(honest, 2))
                self.assertEqual(alice.stamps[self.sim.all_witnesses(Y)[0].pk], [])


class JunkInRotation(unittest.TestCase):
    """A current member answering junk to FREEZE, or a new member to ADOPT, never crashes a rotation."""

    def test_freeze_and_adopt(self):
        for kind, reply in JUNK.items():
            with self.subTest(kind):
                sim = Network()
                X = sim.create_constellation("orion")
                old = sim.all_witnesses(X)
                for w in old:
                    w.registry = Registry()
                    w.registry.add_chain(X, sim.registry.chain(X))
                servers = [WitnessServer(w, admin_token=TOKEN).start() for w in old]
                proxies = []
                try:
                    proxies.append(JunkProxy(servers[0].url))
                    net = RemoteNetwork({X: [proxies[0].url] + [s.url for s in servers[1:]]}, timeout=5)
                    proxies[0].junk = {"freeze": reply}
                    new = []
                    for _ in range(4):
                        reg = Registry()
                        reg.add_chain(X, sim.registry.chain(X))
                        servers.append(WitnessServer(Witness(KeyPair.generate(), reg, sim.clock),
                                                     admin_token=TOKEN).start())
                        new.append(servers[-1].url)
                    proxies.append(JunkProxy(new[0]))
                    proxies[1].junk = {"adopt": reply}
                    try:
                        self.assertEqual(net.rotate(X, [proxies[1].url] + new[1:], TOKEN), 1)
                    except RotationIncomplete as e:
                        self.assertEqual(e.pending, [proxies[1].url])
                finally:
                    for s in proxies + servers:
                        s.stop()


class JunkStandby(unittest.TestCase):
    """One standby member of four answers junk: acks, settling, probes and succession still work."""

    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion", successor={"n": 4, "dead_man": DEAD})
        self.servers = []
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        for w in self.sim.all_witnesses(self.X):
            w.registry = self._registry()
            self.servers.append(WitnessServer(w, admin_token=TOKEN).start())
        self.member_urls = [s.url for s in self.servers]
        self.committee_urls = []
        for m in self.sim.committees[self.X]:
            m.registry = self._registry()
            s = StandbyServer(m, admin_token=TOKEN).start()
            self.servers.append(s)
            self.committee_urls.append(s.url)
        self.proxy = JunkProxy(self.committee_urls[0])
        self.addCleanup(self.proxy.stop)
        self.urls = [self.proxy.url] + self.committee_urls[1:]

    def _registry(self):
        reg = Registry()
        reg.add_chain(self.X, self.sim.registry.chain(self.X))
        return reg

    def test_payments_and_settling(self):
        for kind, reply in JUNK.items():
            for junk in ({"*": reply}, {p: reply for p in ("mirror", "status", "note_release")}):
                with self.subTest(kind=kind, info="junk" if "*" in junk else "honest"):
                    self.proxy.junk = junk
                    net = RemoteNetwork({self.X: self.member_urls}, committees={self.X: self.urls}, timeout=5)
                    alice = Wallet("alice", net, self.X, clock=self.sim.clock)
                    bob = Wallet("bob", net, self.X, clock=self.sim.clock)
                    usd = alice.issue("USD", 100)
                    alice.pay(bob, usd, 40)
                    a = bob.address()
                    refs, outputs = alice.payment_outputs(usd, 5, a)
                    header, body, tid = alice.prepare(refs, outputs)
                    alice.authorise(header, body)
                    self.sim.clock.advance(alice.pledge_ttl + alice.max_skew + 1)
                    alice.release_expired_pledges()
                    self.assertNotIn(tid, alice.pending)
                    done = tid in alice.dossier.transitions
                    self.assertTrue(done or all(p[1] != tid for p in alice.pledged.values()))

    def test_a_slow_member_does_not_delay_the_others(self):
        """Before: the prober asked members one after another, so a member that stalled each of
        its replies to the deadline kept every later member from being heard for that long
        (longer than a short ``dead_man``: the standby member would think the version dead)."""
        member = JunkProxy(self.member_urls[0])
        self.addCleanup(member.stop)
        stop = threading.Event()
        self.addCleanup(stop.set)

        def stall(h):
            stop.wait(30)

        member.junk = {"*": stall}
        prober, standby = self.servers[4], self.sim.committees[self.X][0]
        standby.heard.clear()
        t = threading.Thread(target=prober.probe, args=([member.url] + self.member_urls[1:],), daemon=True)
        t.start()
        t.join(3)
        self.assertEqual(len(standby.heard), 3, "honest members were not heard while one member stalled")
        stop.set()

    def test_a_junk_member_does_not_blind_the_prober(self):
        """Before: a member whose INFO or HEARTBEAT reply was malformed raised out of
        ``StandbyServer.probe``, discarding every other member's answer of that round, so one
        Byzantine member within f could make a standby member declare a live version dead."""
        member = JunkProxy(self.member_urls[0])
        self.addCleanup(member.stop)
        prober = self.servers[4]
        urls = [member.url] + self.member_urls[1:]
        for kind, reply in JUNK.items():
            for path in ("info", "heartbeat"):
                with self.subTest(kind=kind, path=path):
                    member.junk = {path: reply}
                    self.assertEqual(prober.probe(urls), 3)

    def test_succession_with_a_junk_standby_member(self):
        alice = Wallet("alice", RemoteNetwork({self.X: self.member_urls}, committees={self.X: self.committee_urls}),
                       self.X)
        alice.issue("USD", 100)
        for s in self.servers[:4]:
            s.stop()
        self.servers = self.servers[4:]
        self.sim.clock.advance(DEAD + 1)
        for kind, reply in JUNK.items():
            for path in ("info", "succeed", "*"):
                with self.subTest(kind=kind, path=path):
                    self.proxy.junk = {path: reply}
                    net = RemoteNetwork({self.X: self.member_urls}, committees={self.X: self.urls}, timeout=5,
                                        registry=self._registry())
                    # Read-only: every phase up to signing, which fences members (so stop there).
                    chain, cur = net._current(self.X)
                    nxt = charter_body(cur["name"], cur["version"] + 1, [KeyPair.generate().pk], charter_hash(cur))
                    agree = 0
                    for url in self.urls:
                        try:
                            info = RemoteStandby(url, 5).info()
                        except Rejected:
                            continue
                        agree += info.get("dead") is True
                    self.assertGreaterEqual(agree, 3)
                    self.assertIsNotNone(nxt)
        self.proxy.junk = {"succeed": JUNK["ok list"]}
        net = RemoteNetwork({self.X: self.member_urls}, committees={self.X: self.urls}, timeout=5,
                            registry=self._registry())
        new = []
        for _ in range(4):
            s = WitnessServer(Witness(KeyPair.generate(), self._registry(), self.sim.clock), admin_token=TOKEN).start()
            self.servers.append(s)
            new.append(s.url)
        self.assertEqual(net.succeed(self.X, new, TOKEN), 1)


if __name__ == "__main__":
    unittest.main()
