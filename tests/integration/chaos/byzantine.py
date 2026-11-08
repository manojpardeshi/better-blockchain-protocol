"""A Byzantine witness process for the chaos harness (never part of the product).

    python -m tests.integration.chaos.byzantine --key K --registry R --constellation CID \\
        --store S --host H --port P --modes equivocate,lie,withhold,garbage [--seed N]

It holds a real member key of the constellation, so its votes count toward seals, and it
misbehaves per request, choosing among the enabled ``--modes`` with a seeded RNG:

* ``equivocate``: votes for every authorised SPEND, whatever it voted before at that
  (sigil, gen): it never answers ``conflict`` and signs as many tids as it is asked to.
* ``lie``: answers STATUS with "nothing bound, no votes" (SPEC §4 rule 3 trusts STATUS).
* ``withhold``: serves no proofs, only the genesis charter, and accepts no gossip.
* ``garbage``: malformed or oversized replies: invalid JSON, wrong types where a vote or a
  status is expected, a vote with a bad signature or for another tid, a reply of
  ``--oversize`` bytes, a stalled reply.
* ``silent``: accepts the connection and never answers.
* ``badstatus``: every STATUS reply is ``{"gen": 0, "tid": null, "votes": [0]}`` (deterministic).
* ``always``: never fall back to honest behaviour (by default a quarter of the requests are
  answered honestly, so a Byzantine member mostly looks alive).

With no applicable mode a request is answered like an honest witness would (an in-memory
``Witness``), so a Byzantine member mostly looks alive. Its store is never written: a
Byzantine witness may forget anything.
"""

import argparse
import json
import random
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from sigil.witness import Conflict, Rejected, Witness, authorises
from sigil.witnessd import load_key, load_registry


class Byzantine:
    def __init__(self, kp, registry, cid: str, modes: set, seed: int, oversize: int):
        self.w = Witness(kp, registry, lambda: int(time.time()))
        chain = registry.chain(cid)
        version = max(i for i, c in enumerate(chain) if kp.pk in c["body"]["witnesses"])
        self.w.cid, self.w.version = cid, version
        self.modes = modes
        self.rng = random.Random(seed)
        self.lock = threading.Lock()
        self.oversize = oversize
        self.genesis = chain[:1]
        self.votes: dict = {}  # (sigil, gen, tid) -> vote, everything it ever signed

    def pick(self, *wanted: str) -> str | None:
        """One of ``wanted`` that is enabled (or None for honest behaviour), at random."""
        live = [m for m in wanted if m in self.modes]
        with self.lock:
            if not live or ("always" not in self.modes and self.rng.random() < 0.25):
                return None
            return self.rng.choice(live)

    def garbage(self, kind: str):
        """A malformed reply: ``(status, raw bytes)``."""
        with self.lock:
            choice = self.rng.randrange(9)
        if choice == 0:
            return 200, b"{not json"
        if choice == 1:
            return 200, json.dumps({"ok": "a string, not a %s" % kind}).encode()
        if choice == 2:
            return 200, json.dumps({"ok": [1, 2, 3]}).encode()
        if choice == 3:
            return 200, json.dumps({"ok": {"gen": "zero", "tid": 7, "votes": "none"}}).encode()
        if choice == 4:
            return 200, json.dumps({"ok": {"gen": 0, "tid": None, "votes": [1, None, "x", {"gen": 0}]}}).encode()
        if choice == 5:
            return 409, json.dumps({"error": "conflict", "message": "x", "vote": [1, 2]}).encode()
        if choice == 6:
            pad = "A" * self.oversize
            return 200, json.dumps({"ok": {"pad": pad}}).encode()
        if choice == 7:
            return 200, json.dumps({"ok": None}).encode()
        return 500, b"\x00\xff garbage"

    def spend(self, req: dict):
        mode = self.pick("equivocate", "garbage", "silent")
        if mode == "silent":
            return "silent", None
        if mode == "garbage":
            return "raw", self.garbage("vote")
        if mode == "equivocate":
            auth = {k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}
            bound = authorises(req.get("sigil"), auth)
            if bound is None:
                return "json", (403, {"error": "rejected", "message": "lock not satisfied", "vote": None})
            g, tid = bound
            with self.lock:
                v = self.votes.get((req["sigil"], g, tid)) or self.w._vote(req["sigil"], g, tid)
                self.votes[(req["sigil"], g, tid)] = v
            return "json", (200, {"ok": v})
        with self.lock:
            try:
                v = self.w.spend(req)
            except Conflict as e:
                return "json", (409, {"error": "conflict", "message": str(e), "vote": e.vote})
            except Rejected as e:
                return "json", (403, {"error": "rejected", "message": str(e), "vote": None})
            self.votes[(req["sigil"], v["gen"], v["tid"])] = v
            return "json", (200, {"ok": v})

    def status(self, sigil: str):
        if "badstatus" in self.modes:  # deterministic: a vote list holding a non-object
            return "json", (200, {"ok": {"gen": 0, "tid": None, "votes": [0]}})
        mode = self.pick("lie", "garbage", "silent")
        if mode == "silent":
            return "silent", None
        if mode == "garbage":
            return "raw", self.garbage("status")
        if mode == "lie":
            return "json", (200, {"ok": {"gen": 0, "tid": None, "votes": []}})
        with self.lock:
            st = self.w.status(sigil)
            st["votes"] = [v for (s, _g, _t), v in self.votes.items() if s == sigil]
        return "json", (200, {"ok": st})


def serve(b: Byzantine, host: str, port: int) -> None:
    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.0"

        def log_message(self, *args):
            pass

        def _send(self, status: int, data: bytes):
            try:
                self.send_response(status)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)
            except OSError:
                pass

        def _out(self, result):
            how, what = result
            if how == "silent":
                time.sleep(60)
                return
            if how == "raw":
                return self._send(*what)
            self._send(what[0], json.dumps(what[1]).encode())

        def do_GET(self):
            path = self.path.removeprefix("/v0/")
            w = b.w
            if path == "info":
                return self._out(("json", (200, {"ok": {"pk": w.pk, "constellation": w.cid, "version": w.version,
                                                         "frozen": False, "stamps": None}})))
            if path == "charters":
                if b.pick("withhold"):
                    return self._out(("json", (200, {"ok": {w.cid: b.genesis}})))
                reg = w.registry
                return self._out(("json", (200, {"ok": {c: reg.chain(c) for c in reg.ids()}})))
            if path == "proofs":
                if b.pick("garbage") == "garbage":
                    return self._out(("raw", b.garbage("proofs")))
                return self._out(("json", (200, {"ok": {"proofs": [], "forks": []}})))
            self._out(("json", (404, {"error": "bad_request", "message": "unknown path", "vote": None})))

        def do_POST(self):
            path = self.path.removeprefix("/v0/")
            try:
                n = int(self.headers.get("Content-Length", "0"))
                body = json.loads(self.rfile.read(n) or b"{}")
            except ValueError:
                return self._out(("json", (400, {"error": "bad_request", "message": "bad body", "vote": None})))
            try:
                if path == "spend":
                    return self._out(b.spend(body["request"]))
                if path == "status":
                    return self._out(b.status(body["sigil"]))
                if path == "heartbeat":
                    if b.pick("silent", "garbage"):
                        return self._out(("raw", (500, b"no")))
                    return self._out(("json", (200, {"ok": b.w.heartbeat(body["challenge"])})))
                if path == "gossip":
                    if b.pick("withhold"):
                        return self._out(("json", (200, {"ok": {"charters": 0, "proofs": 0, "forks": 0}})))
                    with b.lock:
                        for cid, chain in (body.get("charters") or {}).items():
                            try:
                                b.w.registry.add_chain(cid, chain)
                            except ValueError:
                                pass
                    return self._out(("json", (200, {"ok": {"charters": 0, "proofs": 0, "forks": 0}})))
                if path == "release":
                    with b.lock:
                        try:
                            return self._out(("json", (200, {"ok": b.w.release(body["sigil"], body["proof"])})))
                        except Rejected as e:
                            return self._out(("json", (403, {"error": "rejected", "message": str(e), "vote": None})))
            except (KeyError, TypeError, ValueError, AttributeError) as e:
                return self._out(("json", (400, {"error": "bad_request", "message": str(e), "vote": None})))
            self._out(("json", (403, {"error": "rejected", "message": "not served", "vote": None})))

    class Server(ThreadingHTTPServer):
        daemon_threads = True
        allow_reuse_address = True

    Server((host, port), Handler).serve_forever()


def main(argv=None) -> None:
    p = argparse.ArgumentParser()
    for a in ("--key", "--registry", "--constellation", "--store"):
        p.add_argument(a, required=True)
    p.add_argument("--host", default="127.0.0.1")
    p.add_argument("--port", type=int, required=True)
    p.add_argument("--modes", default="equivocate,lie,withhold,garbage")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--oversize", type=int, default=24 << 20)
    p.add_argument("--admin-token")
    args, _unknown = p.parse_known_args(argv)
    b = Byzantine(load_key(args.key), load_registry(args.registry), args.constellation,
                  set(filter(None, args.modes.split(","))), args.seed, args.oversize)
    print(f"byzantine {b.w.pk[:12]} modes={sorted(b.modes)} on {args.host}:{args.port}", flush=True)
    serve(b, args.host, args.port)


if __name__ == "__main__":
    main()
