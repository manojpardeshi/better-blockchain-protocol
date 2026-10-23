"""Wire protocol v0: witnesses over HTTP, and the clients that talk to them.

Every call is ``POST /v0/<method>`` with a JSON object body; every reply is
``{"ok": result}`` or ``{"error": "rejected" | "conflict" | "bad_request",
"message": str, "vote": vote | null}``. Big integers (blinded stamp values)
travel as hex strings so any JSON implementation can carry them. See
docs/WIRE.md.

``RemoteWitness`` has the same interface as ``Witness`` and ``RemoteNetwork``
the same as ``Network``, so wallets work unchanged against a real network.
Nothing a remote witness says is trusted: votes, seals and proofs are
verified exactly as they are in-process.
"""

import json
import threading
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from .charter import Registry
from .gossip import GossipStore
from .witness import Conflict, Rejected, Witness

MAX_BODY = 1 << 20
MAX_RESPONSE = 16 << 20   # largest gossip snapshot a client reads from one witness


# ------------------------------------------------------------------ server

class WitnessServer:
    """Serves one ``Witness`` over HTTP. Calls are serialised per witness."""

    def __init__(self, witness: Witness, host: str = "127.0.0.1", port: int = 0):
        self.witness = witness
        self._lock = threading.Lock()
        # Gossip shares the witness's registry: a verified rotation learned
        # by gossip is immediately what the witness serves and checks against.
        self.gossip = GossipStore(witness.registry)
        server = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args):  # quiet
                pass

            def do_GET(self):
                if self.path == "/v0/info":
                    return self._reply(200, {"ok": server.info()})
                if self.path == "/v0/charters":
                    reg = server.witness.registry
                    return self._reply(200, {"ok": {cid: reg.chain(cid) for cid in reg.ids()}})
                if self.path == "/v0/proofs":
                    with server._lock:
                        snap = {"proofs": list(server.gossip.proofs.values()),
                                "forks": list(server.gossip.forks.values())}
                    return self._reply(200, {"ok": snap})
                self._reply(404, {"error": "bad_request", "message": "unknown path", "vote": None})

            def do_POST(self):
                try:
                    n = int(self.headers.get("Content-Length", "0"))
                    if not 0 <= n <= MAX_BODY:
                        raise ValueError("body too large")
                    body = json.loads(self.rfile.read(n) or b"{}")
                    if not isinstance(body, dict):
                        raise ValueError("body must be an object")
                    method = self.path.removeprefix("/v0/")
                    result = server.dispatch(method, body)
                    self._reply(200, {"ok": result})
                except Conflict as e:
                    self._reply(409, {"error": "conflict", "message": str(e), "vote": e.vote})
                except Rejected as e:
                    self._reply(403, {"error": "rejected", "message": str(e), "vote": None})
                except (ValueError, KeyError, TypeError, AttributeError) as e:
                    self._reply(400, {"error": "bad_request", "message": str(e), "vote": None})
                except Exception:  # never drop a connection without an answer
                    self._reply(500, {"error": "internal", "message": "internal error", "vote": None})

            def _reply(self, code, obj):
                data = json.dumps(obj).encode()
                self.send_response(code)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)

        self.httpd = ThreadingHTTPServer((host, port), Handler)
        self.httpd.daemon_threads = True
        self._thread = None

    @property
    def url(self) -> str:
        host, port = self.httpd.server_address[:2]
        return f"http://{host}:{port}"

    def info(self) -> dict:
        w = self.witness
        return {"pk": w.pk, "constellation": w.cid, "version": w.version, "frozen": w.frozen,
                "stamps": _pub_out(w.stamps.public) if w.stamps is not None else None}

    def dispatch(self, method: str, body: dict):
        w = self.witness
        with self._lock:
            if method == "spend":
                return w.spend(body["request"])
            if method == "release":
                return w.release(body["sigil"], body["proof"])
            if method == "status":
                return w.status(body["sigil"])
            if method == "sell_stamp":
                return format(w.sell_stamp(int(body["blinded"], 16)), "x")
            if method == "gossip":
                return self.gossip.merge(body)
        raise ValueError(f"unknown method {method!r}")

    def start(self) -> "WitnessServer":
        self._thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)
        self._thread.start()
        return self

    def serve_forever(self) -> None:
        self.httpd.serve_forever()

    def stop(self) -> None:
        self.httpd.shutdown()
        self.httpd.server_close()


def _pub_out(pub: dict) -> dict:
    return {"n": format(pub["n"], "x"), "e": format(pub["e"], "x")}


def _pub_in(pub: dict) -> dict:
    return {"n": int(pub["n"], 16), "e": int(pub["e"], 16)}


# ------------------------------------------------------------------ client

class Unreachable(Rejected):
    """The witness did not answer (network error or timeout)."""


class _RemoteStamps:
    def __init__(self, public: dict):
        self.public = public


class RemoteWitness:
    """A witness reached over HTTP, with the same interface as ``Witness``."""

    def __init__(self, url: str, timeout: float = 5.0):
        self.url = url.rstrip("/")
        self.timeout = timeout
        self.max_response = MAX_RESPONSE  # gossip pulls only: a peer cannot make us buffer more
        info = self._get("info")
        self.pk, self.cid, self.version = info["pk"], info["constellation"], info["version"]
        self.stamps = _RemoteStamps(_pub_in(info["stamps"])) if info["stamps"] else None

    def __repr__(self):
        return f"RemoteWitness({self.url}, {self.pk[:8]})"

    def _get(self, path: str):
        try:
            with urllib.request.urlopen(f"{self.url}/v0/{path}", timeout=self.timeout) as r:
                return json.loads(r.read())["ok"]
        except (urllib.error.URLError, OSError, ValueError) as e:
            raise Unreachable(f"{self.url}: {e}") from e

    def _call(self, method: str, body: dict):
        req = urllib.request.Request(f"{self.url}/v0/{method}", data=json.dumps(body).encode(),
                                     headers={"Content-Type": "application/json"}, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as r:
                return json.loads(r.read())["ok"]
        except urllib.error.HTTPError as e:
            try:
                err = json.loads(e.read())
            except ValueError:
                raise Unreachable(f"{self.url}: HTTP {e.code}") from e
            if err.get("error") == "conflict":
                raise Conflict(err.get("vote")) from e
            raise Rejected(err.get("message", "rejected")) from e
        except (urllib.error.URLError, OSError, ValueError) as e:
            raise Unreachable(f"{self.url}: {e}") from e

    def spend(self, req: dict) -> dict:
        return self._call("spend", {"request": req})

    def release(self, sigil: str, proof: dict) -> int:
        return self._call("release", {"sigil": sigil, "proof": proof})

    def status(self, sigil: str) -> dict:
        return self._call("status", {"sigil": sigil})

    def sell_stamp(self, blinded: int) -> int:
        return int(self._call("sell_stamp", {"blinded": format(blinded, "x")}), 16)

    def charters(self) -> dict:
        return self._get("charters")

    # Gossip (docs/WIRE.md "Gossip"). Nothing pulled is trusted: the caller
    # admits it through a ``GossipStore``, which verifies every item.

    def _get_capped(self, path: str):
        try:
            with urllib.request.urlopen(f"{self.url}/v0/{path}", timeout=self.timeout) as r:
                data = r.read(self.max_response + 1)
            if len(data) > self.max_response:
                raise ValueError("response too large")
            return json.loads(data)["ok"]
        except (urllib.error.URLError, OSError, ValueError, KeyError, TypeError) as e:
            raise Unreachable(f"{self.url}: {e}") from e

    def proofs(self) -> dict:
        """The ``{proofs, forks}`` the witness holds."""
        return self._get_capped("proofs")

    def pull(self) -> dict:
        """Everything the witness can gossip: ``{charters, proofs, forks}``."""
        out = self._get_capped("proofs")
        if not isinstance(out, dict):
            raise Unreachable(f"{self.url}: malformed proofs reply")
        out["charters"] = self._get_capped("charters")
        return out

    def gossip(self, msg: dict) -> dict:
        """Offer ``{charters, proofs, forks}``; returns the counts the witness accepted."""
        return self._call("gossip", msg)


class RemoteNetwork:
    """The address book of a real network: constellation id -> witness URLs.

    Unreachable witnesses are treated like crashed ones. Charter chains are
    fetched from the witnesses and verified before use.
    """

    def __init__(self, directory: dict, *, timeout: float = 5.0, registry: Registry | None = None):
        self.registry = registry or Registry()
        self.timeout = timeout
        self.urls: dict[str, list] = {cid: list(urls) for cid, urls in directory.items()}
        self._clients: dict[str, RemoteWitness] = {}
        self.down: set[str] = set()
        for cid in self.urls:
            self.refresh_charters(cid)

    def _client(self, url: str) -> RemoteWitness | None:
        c = self._clients.get(url)
        if c is None:
            try:
                c = self._clients[url] = RemoteWitness(url, self.timeout)
            except Unreachable:
                return None
        return c

    def refresh_charters(self, cid: str) -> None:
        for url in self.urls.get(cid, []):
            c = self._client(url)
            if c is None:
                continue
            try:
                chains = c.charters()
            except Unreachable:
                continue
            for other, chain in chains.items():
                try:
                    self.registry.add_chain(other, chain)
                except ValueError:
                    pass  # invalid or forked chains are ignored, never trusted

    def all_witnesses(self, cid: str) -> list:
        return [c for c in (self._client(u) for u in self.urls.get(cid, [])) if c is not None]

    def witnesses(self, cid: str) -> list:
        return [w for w in self.all_witnesses(cid) if w.pk not in self.down]

    def find_votes(self, sigil: str) -> list:
        out = []
        for cid in self.urls:
            for w in self.witnesses(cid):
                try:
                    out.extend(w.status(sigil)["votes"])
                except Rejected:
                    pass
        return out
