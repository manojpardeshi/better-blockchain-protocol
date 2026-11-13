"""A Byzantine standby member of a successor committee, for the chaos harness (never part of the product).

    python -m tests.integration.chaos.byzantine_standby --key K --registry R --constellation CID \\
        --store S --host H --port P --modes ackonly,lie,signany,junksnap,norelease [--seed N]

It holds a real committee key, so its acks and its signature on a successor count. Modes:

* ``ackonly``: answers MIRROR with a valid ack but stores nothing (its mirror log stays empty);
* ``lie``: STATUS says "no bindings", and ``/v0/info`` reports ``dead`` as the opposite of the
  truth (a live version dead, a dead one alive);
* ``signany``: SUCCEED signs any successor body at once, cooperative or not, dead or not;
* ``junksnap``: its SUCCEED snapshot is junk: padded and forged entries, made-up sigils, values only
  one implementation can represent, and a forged binding for every sigil it was asked to mirror;
* ``norelease``: refuses every ``note_release``;
* ``garbage``: malformed replies to MIRROR, STATUS and ``/v0/info`` now and then.

Without a mode it behaves like an honest member, in memory (its store is never written).
"""

import argparse
import json
import random
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from sigil.charter import sign_charter
from sigil.succession import Standby
from sigil.witness import Rejected
from sigil.witnessd import load_key, load_registry


class ByzantineStandby:
    def __init__(self, kp, registry, cid: str, modes: set, seed: int):
        self.kp, self.registry, self.cid = kp, registry, cid
        self.m = Standby(kp, registry, lambda: int(time.time()))
        chain = registry.chain(cid)
        versions = [i for i, c in enumerate(chain)
                    if kp.pk in ((c["body"].get("successor") or {}).get("committee") or [])]
        if versions and versions[-1] == 0:
            self.m.enter(cid, 0, [])
        self.modes, self.rng, self.lock = modes, random.Random(seed), threading.Lock()
        self.seen: dict = {}     # sigil -> a request it was asked to mirror

    def roll(self, p: float = 0.3) -> bool:
        with self.lock:
            return self.rng.random() < p

    def info(self):
        if "garbage" in self.modes and self.roll():
            return "raw", (200, b'{"ok": []}')
        with self.lock:
            i = dict(self.m.info(), frozen=False, stamps=None)
        if "lie" in self.modes:
            i["dead"] = not i["dead"]
        return "json", (200, {"ok": i})

    def mirror(self, req):
        if "garbage" in self.modes and self.roll():
            return "raw", (200, b'{"ok": {"member": 5}}')
        with self.lock:
            if isinstance(req, dict) and isinstance(req.get("sigil"), str):
                self.seen.setdefault(req["sigil"], req)
            if "ackonly" in self.modes:
                m = self.m
                saved = (dict(m.mirror), set(m.mirrored), {k: set(v) for k, v in m._by_sigil.items()}, dict(m._tids))
                try:
                    return "json", (200, {"ok": m.mirror_bind(req)})
                finally:   # it signs, then forgets
                    m.mirror, m.mirrored, m._by_sigil, m._tids = saved
            return "json", (200, {"ok": self.m.mirror_bind(req)})

    def status(self, sigil):
        if "garbage" in self.modes and self.roll():
            return "raw", (200, b'{"ok": {"bindings": 7}}')
        if "lie" in self.modes:
            return "json", (200, {"ok": {"bindings": []}})
        with self.lock:
            return "json", (200, {"ok": self.m.status(sigil)})

    def succeed(self, body):
        nxt = body["charter"]
        with self.lock:
            if "signany" in self.modes:
                sig, snap = sign_charter(self.kp, nxt), self.m.snapshot()
            else:
                sig, snap = self.m.succeed(nxt, body.get("sigs"))
        if "junksnap" in self.modes:
            snap = self.junk(snap)
        return "raw", (200, json.dumps({"ok": {"sig": sig, "snapshot": snap}}).encode())

    def junk(self, snap: dict) -> dict:
        out = {s: list(log) + [7, {"kind": "bind", "auth": None}, {"kind": "zzz", "pad": "p" * 4096},
                               {"kind": "release", "tid": "00" * 32, "header": {}, "proof": {}},
                               {"kind": "seal", "seal": {"votes": []}}, {"kind": "x", "v": float("nan")},
                               {"kind": "x", "v": 1 << 140}]
               for s, log in snap.items()}
        with self.lock:
            seen = list(self.seen.items())
        for s, req in seen:
            forged = json.loads(json.dumps({k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}))
            if isinstance(forged.get("header"), dict):
                forged["header"]["body"] = "ff" * 32            # another tid: the owner's signature fails
            out.setdefault(s, []).append({"kind": "bind", "gen": 0, "auth": forged})
        for k in range(200):
            out[f"{k:064x}"] = [{"kind": "bind", "gen": 0, "auth": {"n": k}}]
        return out


def serve(b: ByzantineStandby, host: str, port: int) -> None:
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
            if how == "raw":
                return self._send(*what)
            self._send(what[0], json.dumps(what[1]).encode())

        def _err(self, code, kind, msg):
            self._out(("json", (code, {"error": kind, "message": msg, "vote": None})))

        def do_GET(self):
            path = self.path.removeprefix("/v0/")
            if path == "info":
                return self._out(b.info())
            if path == "charters":
                reg = b.registry
                return self._out(("json", (200, {"ok": {c: reg.chain(c) for c in reg.ids()}})))
            if path == "proofs":
                return self._out(("json", (200, {"ok": {"proofs": [], "forks": []}})))
            self._err(404, "bad_request", "unknown path")

        def do_POST(self):
            path = self.path.removeprefix("/v0/")
            try:
                n = int(self.headers.get("Content-Length", "0"))
                body = json.loads(self.rfile.read(n) or b"{}")
                if path == "mirror":
                    return self._out(b.mirror(body["request"]))
                if path == "status":
                    return self._out(b.status(body["sigil"]))
                if path == "note_release":
                    if "norelease" in b.modes:
                        return self._err(403, "rejected", "not today")
                    with b.lock:
                        return self._out(("json", (200, {"ok": b.m.note_release(body["sigil"], body["entry"])})))
                if path == "gossip":
                    with b.lock:
                        for cid, chain in (body.get("charters") or {}).items():
                            try:
                                b.registry.add_chain(cid, chain)
                            except ValueError:
                                pass
                    return self._out(("json", (200, {"ok": {"charters": 0, "proofs": 0, "forks": 0}})))
                if path == "succeed":
                    return self._out(b.succeed(body))
                if path == "probe":
                    return self._out(("json", (200, {"ok": {"answered": 0}})))
                if path == "standby":
                    with b.lock:
                        b.m.enter(body["constellation"], body["version"], body["snapshots"])
                        return self._out(("json", (200, {"ok": {"constellation": b.m.cid, "version": b.m.version}})))
            except Rejected as e:
                return self._err(403, "rejected", str(e))
            except (KeyError, TypeError, ValueError, AttributeError) as e:
                return self._err(400, "bad_request", str(e))
            self._err(403, "rejected", "not served")

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
    p.add_argument("--modes", default="ackonly,lie")
    p.add_argument("--seed", type=int, default=0)
    args, _unknown = p.parse_known_args(argv)
    b = ByzantineStandby(load_key(args.key), load_registry(args.registry), args.constellation,
                         set(filter(None, args.modes.split(","))), args.seed)
    print(f"byzantine standby {b.kp.pk[:12]} modes={sorted(b.modes)} on {args.host}:{args.port}", flush=True)
    serve(b, args.host, args.port)


if __name__ == "__main__":
    main()
