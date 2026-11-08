"""A fault-injecting HTTP reverse proxy, one in front of each witness or standby member.

Every request a wallet, an operator or a standby member's prober sends to a process goes
through its proxy, which forwards it to the real port and can, per request:

* **drop** it (the connection is closed unanswered: the process never sees it);
* **lose the reply** (the process handled it and persisted its state, the client sees a
  dead connection);
* **delay** it, possibly past the client's timeout, so it reaches the process after the
  client gave up (requests delayed by different amounts are **reordered**);
* **duplicate** it (forwarded twice; the client gets the first answer);
* **hold** it indefinitely, until the harness calls ``deliver_held`` (the "request delayed in
  flight past the authorisation's expiry" scenario of SPEC §4 rule 3);
* refuse or black-hole everything while **partitioned**;
* hand the request to a **kill hook**, which can SIGKILL the process before forwarding, at a
  random offset after forwarding (mid-processing, mid-store-commit) or after the reply came
  back but before it is relayed.

Every request and reply body is passed to an ``Observer`` (``invariants.Observer``), which
extracts the votes, headers and acks in them for the global safety checks. Decisions come
from a ``random.Random`` seeded per proxy, so a run's fault pattern follows its seed (the
interleaving still depends on timing).
"""

import http.client
import json
import random
import socket
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


class Faults:
    """The fault mix of one proxy; the harness changes it while the run goes on."""

    def __init__(self):
        self.p_drop = 0.0          # drop the request before forwarding
        self.p_lose_reply = 0.0    # forward, then close the client connection unanswered
        self.p_delay = 0.0         # delay before forwarding
        self.delay = (0.05, 0.5)   # seconds, uniform
        self.p_dup = 0.0           # forward twice
        self.p_hold = 0.0          # hold until deliver_held()
        self.hold_methods = ("spend",)
        self.partition = None      # None | "refuse" | "blackhole"
        self.only = None           # methods the random faults apply to (None: all)

    def clear(self) -> None:
        self.__init__()

    def as_dict(self) -> dict:
        return dict(vars(self))


class _Server(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True
    request_queue_size = 256


class FaultProxy:
    """Forward ``127.0.0.1:<port>`` to ``backend`` (``(host, port)``) with ``faults``."""

    def __init__(self, name: str, backend: tuple, observer, seed: int, *, client_timeout: float = 2.0):
        self.name = name
        self.backend = backend
        self.observer = observer
        self.faults = Faults()
        self.rng = random.Random(seed)
        self._rng_lock = threading.Lock()
        self.client_timeout = client_timeout  # how long a black-holed client waits before we hang up
        self.kill_hook = None                 # callable(proxy, method, body) -> None | (phase, delay, kill)
        self.hold_filter = None               # callable(method, body) -> bool: hold these requests
        self.held: list = []                  # (method, path, headers, body)
        self._held_lock = threading.Lock()
        self.stats: dict = {}
        self._stats_lock = threading.Lock()
        proxy = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"
            timeout = 30

            def log_message(self, *args):
                pass

            def do_GET(self):
                proxy._handle(self, "GET", b"")

            def do_POST(self):
                try:
                    n = int(self.headers.get("Content-Length", "0"))
                except ValueError:
                    n = 0
                body = self.rfile.read(n) if n > 0 else b""
                proxy._handle(self, "POST", body)

        self.httpd = _Server(("127.0.0.1", 0), Handler)
        self.port = self.httpd.server_address[1]
        self.url = f"http://127.0.0.1:{self.port}"
        threading.Thread(target=self.httpd.serve_forever, daemon=True, name=f"proxy-{name}").start()

    # ------------------------------------------------------------ helpers

    def _count(self, key: str, n: int = 1) -> None:
        with self._stats_lock:
            self.stats[key] = self.stats.get(key, 0) + n

    def _roll(self, p: float) -> bool:
        if p <= 0:
            return False
        with self._rng_lock:
            return self.rng.random() < p

    def _uniform(self, lo: float, hi: float) -> float:
        with self._rng_lock:
            return self.rng.uniform(lo, hi)

    def _forward(self, verb: str, path: str, headers: dict, body: bytes, timeout: float = 30.0):
        """One request to the backend: ``(status, reply headers, reply body)`` or None."""
        conn = http.client.HTTPConnection(*self.backend, timeout=timeout)
        try:
            conn.request(verb, path, body=body if verb == "POST" else None, headers=headers)
            r = conn.getresponse()
            data = r.read()
            return r.status, dict(r.getheaders()), data
        except (OSError, http.client.HTTPException):
            return None
        finally:
            conn.close()

    def _observe(self, method: str, body: bytes, reply) -> None:
        try:
            req = json.loads(body) if body else None
        except ValueError:
            req = None
        rep = None
        if reply is not None:
            try:
                rep = json.loads(reply[2])
            except ValueError:
                rep = None
        try:
            self.observer.record(self.name, method, req, None if reply is None else reply[0], rep)
        except Exception as e:  # noqa: BLE001 - observation must never break the traffic
            self._count(f"observer-error:{type(e).__name__}")

    @staticmethod
    def _relay(handler, reply) -> None:
        status, headers, data = reply
        try:
            handler.send_response(status)
            for k in ("Content-Type", "Retry-After"):
                if k in headers:
                    handler.send_header(k, headers[k])
            handler.send_header("Content-Length", str(len(data)))
            handler.end_headers()
            handler.wfile.write(data)
        except OSError:
            pass

    @staticmethod
    def _hang_up(handler) -> None:
        try:
            handler.connection.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        handler.close_connection = True

    # ------------------------------------------------------------ the hot path

    def _handle(self, handler, verb: str, body: bytes) -> None:
        path = handler.path
        method = path.removeprefix("/v0/")
        headers = {k: v for k, v in handler.headers.items() if k.lower() in ("content-type", "authorization")}
        self._count("requests")
        f = self.faults
        if f.partition is not None:
            self._count(f"partition-{f.partition}")
            if f.partition == "blackhole":
                time.sleep(self.client_timeout)
            return self._hang_up(handler)
        faulty = f.only is None or method in f.only
        hf = self.hold_filter
        if (hf is not None and hf(method, body)) or (faulty and method in f.hold_methods and self._roll(f.p_hold)):
            with self._held_lock:
                self.held.append((verb, path, headers, body))
            self._count("held")
            time.sleep(self.client_timeout)  # the client gives up
            return self._hang_up(handler)
        if faulty and self._roll(f.p_drop):
            self._count("dropped")
            return self._hang_up(handler)
        if faulty and self._roll(f.p_delay):
            d = self._uniform(*f.delay)
            self._count("delayed")
            time.sleep(d)
        plan = self.kill_hook(self, method, body) if self.kill_hook is not None else None
        if plan is not None and plan[0] == "before":
            self._count("kill-before")
            plan[2]()
        if plan is not None and plan[0] == "during":
            # Forward, and kill the process ``plan[1]`` seconds after the request left.
            self._count("kill-during")
            result: list = []
            t = threading.Thread(target=lambda: result.append(self._forward(verb, path, headers, body)))
            t.start()
            time.sleep(plan[1])
            plan[2]()
            t.join()
            reply = result[0] if result else None
        else:
            reply = self._forward(verb, path, headers, body)
        self._observe(method, body, reply)
        if faulty and reply is not None and self._roll(f.p_dup):
            self._count("duplicated")
            self._observe(method, body, self._forward(verb, path, headers, body))
        if plan is not None and plan[0] == "after":
            self._count("kill-after")
            plan[2]()
            return self._hang_up(handler)
        if reply is None:
            self._count("backend-down")
            return self._hang_up(handler)
        if faulty and self._roll(f.p_lose_reply):
            self._count("reply-lost")
            return self._hang_up(handler)
        self._relay(handler, reply)

    # ------------------------------------------------------------ control

    def deliver_held(self, keep=None) -> int:
        """Forward every held request now (those ``keep(method, body)`` selects, default all)."""
        with self._held_lock:
            go = [h for h in self.held if keep is None or keep(h[1].removeprefix("/v0/"), h[3])]
            self.held = [h for h in self.held if h not in go]
        for verb, path, headers, body in go:
            reply = self._forward(verb, path, headers, body)
            self._observe(path.removeprefix("/v0/"), body, reply)
            self._count("held-delivered")
        return len(go)

    def drop_held(self) -> int:
        with self._held_lock:
            n, self.held = len(self.held), []
        return n

    def stop(self) -> None:
        self.httpd.shutdown()
        self.httpd.server_close()
