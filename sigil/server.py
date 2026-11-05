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

Rotation (SPEC §5.4) is exposed as ``POST /v0/freeze`` and ``POST /v0/adopt``.
Freezing is irreversible, so both are operator calls: they need
``Authorization: Bearer <admin token>`` and are disabled on a witness
started without one. ``RemoteNetwork.rotate`` drives a rotation over them.
"""

import hmac
import json
import threading
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from .charter import Registry, charter_body, charter_hash, quorum, successor_clause
from .crypto import verify
from .gossip import GossipStore
from .ratelimit import (DEFAULT_BURST, DEFAULT_RATE, IDLE_TIMEOUT, MAX_CLIENT_CONNECTIONS, MAX_CONNECTIONS,
                        ConnectionLimiter, RateLimiter, client_key, is_loopback)
from .witness import Conflict, Rejected, Witness

MAX_BODY = 1 << 20
MAX_ADMIN_BODY = 256 << 20  # ADOPT carries every predecessor's evidence; read only once authorised
MAX_RESPONSE = 16 << 20   # largest gossip snapshot a client reads from one witness
ADMIN_METHODS = ("freeze", "adopt")


# ------------------------------------------------------------------ server

class _HTTPServer(ThreadingHTTPServer):
    """A threading HTTP server that refuses connections over its caps (closed unread)."""

    daemon_threads = True
    request_queue_size = 128  # the default of 5 drops bursts of connects (clients retry after 1 s)

    def __init__(self, addr, handler, conns: ConnectionLimiter):
        self.conns = conns
        super().__init__(addr, handler)

    def process_request(self, request, client_address):
        key = client_key(client_address[0])
        if not self.conns.acquire(key):
            self.shutdown_request(request)
            return
        try:
            super().process_request(request, client_address)
        except BaseException:
            self.conns.release(key)
            raise

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            self.conns.release(client_key(client_address[0]))


class WitnessServer:
    """Serves one ``Witness`` over HTTP. Calls are serialised per witness.

    ``admin_token`` enables the rotation calls (``freeze``, ``adopt``) for
    requests carrying ``Authorization: Bearer <admin_token>``.

    ``rate_limit`` is the admission control of docs/WIRE.md: requests per
    second per client (``sigil.ratelimit``), with bursts of ``rate_burst``.
    ``None`` (the default) means ``DEFAULT_RATE`` on a non-loopback ``host``
    and no limit on loopback; ``0`` means no limit. Rotation calls are never
    limited (they are refused before their body is read without the token).
    """

    admin_methods = ADMIN_METHODS

    def __init__(self, witness: Witness, host: str = "127.0.0.1", port: int = 0, *,
                 admin_token: str | None = None, rate_limit: float | None = None,
                 rate_burst: int = DEFAULT_BURST):
        self.witness = witness
        self.admin_token = admin_token
        if rate_limit is None:
            rate_limit = 0 if is_loopback(host) else DEFAULT_RATE
        self.limiter = RateLimiter(rate_limit, rate_burst) if rate_limit > 0 else None
        self._lock = threading.Lock()
        # Gossip shares the witness's registry: a verified rotation learned
        # by gossip is immediately what the witness serves and checks against.
        self.gossip = GossipStore(witness.registry)
        server = self

        class Handler(BaseHTTPRequestHandler):
            timeout = IDLE_TIMEOUT  # a silent or slow client is dropped, never waited on forever

            def log_message(self, *args):  # quiet
                pass

            def _admitted(self, method: str, body: bool) -> bool:
                """Charge the client one token; answer 429 if it has none left."""
                if server.limiter is None or method in server.admin_methods:
                    return True
                wait = server.limiter.admit(client_key(self.client_address[0]))
                if not wait:
                    return True
                if body:  # read (and drop) what was sent, so the client reliably gets the answer
                    try:
                        left = int(self.headers.get("Content-Length", "0"))
                    except ValueError:
                        left = 0
                    left = max(0, min(left, MAX_BODY))
                    while left > 0:
                        chunk = self.rfile.read(min(left, 1 << 16))
                        if not chunk:
                            break
                        left -= len(chunk)
                self._reply(429, {"error": "rejected", "message": "rate limited", "vote": None},
                            {"Retry-After": str(wait)})
                return False

            def do_GET(self):
                if not self._admitted(self.path.removeprefix("/v0/"), False):
                    return
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
                if not self._admitted(self.path.removeprefix("/v0/"), True):
                    return
                try:
                    method = self.path.removeprefix("/v0/")
                    admin = method in server.admin_methods
                    if admin:  # before reading the (large) body
                        server.check_admin(self.headers.get("Authorization"))
                    n = int(self.headers.get("Content-Length", "0"))
                    if not 0 <= n <= (MAX_ADMIN_BODY if admin else MAX_BODY):
                        raise ValueError("body too large")
                    body = json.loads(self.rfile.read(n) or b"{}")
                    if not isinstance(body, dict):
                        raise ValueError("body must be an object")
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

            def _reply(self, code, obj, headers=None):
                data = json.dumps(obj).encode()
                self.send_response(code)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                for k, v in (headers or {}).items():
                    self.send_header(k, v)
                self.end_headers()
                self.wfile.write(data)

        conns = ConnectionLimiter(MAX_CONNECTIONS, MAX_CLIENT_CONNECTIONS if self.limiter is not None else None)
        self.httpd = _HTTPServer((host, port), Handler, conns)
        self._thread = None

    @property
    def url(self) -> str:
        host, port = self.httpd.server_address[:2]
        return f"http://{host}:{port}"

    def info(self) -> dict:
        w = self.witness
        return {"pk": w.pk, "constellation": w.cid, "version": w.version, "frozen": w.frozen,
                "stamps": _pub_out(w.stamps.public) if w.stamps is not None else None}

    def check_admin(self, header) -> None:
        """Refuse a rotation call unless it carries this server's admin token."""
        if self.admin_token is None:
            raise Rejected("rotation calls are disabled on this witness (no admin token)")
        want = f"Bearer {self.admin_token}".encode()
        if not isinstance(header, str) or not hmac.compare_digest(header.encode(), want):
            raise Rejected("bad admin token")

    def dispatch(self, method: str, body: dict):
        w = self.witness
        with self._lock:
            if method in ADMIN_METHODS:
                return self._admin(method, body)
            if method == "spend":
                return w.spend(body["request"])
            if method == "release":
                return w.release(body["sigil"], body["proof"])
            if method == "status":
                return w.status(body["sigil"])
            if method == "heartbeat":
                return w.heartbeat(body["challenge"])
            if method == "sell_stamp":
                return format(w.sell_stamp(int(body["blinded"], 16)), "x")
            if method == "gossip":
                return self.gossip.merge(body)
        raise ValueError(f"unknown method {method!r}")

    def _admin(self, method: str, body: dict):
        """Rotation calls (the caller holds the lock and has checked the admin token)."""
        w = self.witness
        if method == "freeze":
            sig, snapshot = w.freeze(body["charter"])
            return {"sig": sig, "snapshot": snapshot}
        # adopt: once, on a witness that has not joined any charter version.
        cid, version, snapshots = body["constellation"], body["version"], body["snapshots"]
        if not isinstance(snapshots, list):
            raise ValueError("snapshots must be a list")
        if w.cid is not None:
            if (w.cid, w.version) == (cid, version):
                return {"constellation": w.cid, "version": w.version}  # a retried ADOPT
            raise Rejected("already a member of a charter version: ADOPT runs once, on a fresh witness")
        w.adopt(cid, version, snapshots)
        return {"constellation": w.cid, "version": w.version}

    def start(self) -> "WitnessServer":
        self._thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)
        self._thread.start()
        return self

    def serve_forever(self) -> None:
        self.httpd.serve_forever()

    def stop(self) -> None:
        self.httpd.shutdown()
        self.httpd.server_close()


STANDBY_ADMIN_METHODS = ("standby", "succeed", "probe")


class StandbyServer(WitnessServer):
    """Serves one ``Standby`` (a successor-committee member, SPEC §5.5) over HTTP.

    Calls: ``mirror`` (a client's binding, answered with a mirror ack),
    ``note_release``, ``gossip`` (to learn charter versions), and the operator
    calls ``standby`` (enter standby with a handover), ``succeed`` (sign a successor
    and fence) and ``probe`` (challenge members for heartbeats now). ``members``
    are witness URLs probed every ``probe_every`` seconds in the background.
    Admission control is the witness server's (``rate_limit``, ``rate_burst``);
    the operator calls are never limited.
    """

    admin_methods = STANDBY_ADMIN_METHODS

    def __init__(self, standby, host: str = "127.0.0.1", port: int = 0, *, admin_token: str | None = None,
                 members: list | None = None, probe_every: float | None = None,
                 rate_limit: float | None = None, rate_burst: int = DEFAULT_BURST):
        super().__init__(standby, host, port, admin_token=admin_token, rate_limit=rate_limit,
                         rate_burst=rate_burst)
        self.standby = standby
        self.members = list(members or [])
        self.probe_every = probe_every
        self._stopping = threading.Event()

    def info(self) -> dict:
        return dict(self.standby.info(), frozen=False, stamps=None)

    def probe(self, urls: list) -> int:
        """Challenge each member at ``urls``; network calls happen outside the lock."""
        import secrets
        answers = []
        for url in urls:
            challenge = secrets.token_hex(16)
            try:
                answers.append((RemoteWitness(url, 5.0).heartbeat(challenge), challenge))
            except Rejected:
                continue
        with self._lock:
            return sum(self.standby.observe(hb, ch) for hb, ch in answers)

    def dispatch(self, method: str, body: dict):
        s = self.standby
        if method == "probe":
            urls = body.get("urls", self.members)
            if not isinstance(urls, list) or not all(isinstance(u, str) for u in urls):
                raise ValueError("urls must be a list of strings")
            return {"answered": self.probe(urls)}
        with self._lock:
            if method == "mirror":
                return s.mirror_bind(body["request"])
            if method == "note_release":
                return s.note_release(body["sigil"], body["entry"])
            if method == "gossip":
                return self.gossip.merge(body)
            if method == "standby":
                if not isinstance(body["snapshots"], list):
                    raise ValueError("snapshots must be a list")
                s.enter(body["constellation"], body["version"], body["snapshots"])
                return {"constellation": s.cid, "version": s.version}
            if method == "succeed":
                sig, snapshot = s.succeed(body["charter"], body.get("sigs"))
                return {"sig": sig, "snapshot": snapshot}
        raise ValueError(f"unknown method {method!r}")

    def start(self) -> "StandbyServer":
        super().start()
        if self.probe_every and self.members:
            def loop():
                while not self._stopping.wait(self.probe_every):
                    try:
                        self.probe(self.members)
                    except Exception:  # noqa: BLE001 - a prober never takes the server down
                        pass
            threading.Thread(target=loop, daemon=True).start()
        return self

    def stop(self) -> None:
        self._stopping.set()
        super().stop()


def _pub_out(pub: dict) -> dict:
    return {"n": format(pub["n"], "x"), "e": format(pub["e"], "x")}


def _pub_in(pub: dict) -> dict:
    return {"n": int(pub["n"], 16), "e": int(pub["e"], 16)}


# ------------------------------------------------------------------ client

class Unreachable(Rejected):
    """The witness did not answer (network error or timeout)."""


class RotationIncomplete(RuntimeError):
    """The new charter version is in force, but some new members have not adopted.

    ``pending`` lists their URLs. A re-used key that did not sign cannot bring
    its own votes (SPEC §5.4), so it is left waiting; adopt it once its old
    process can be frozen (freezing again for the same successor returns the
    evidence again).
    """

    def __init__(self, version: int, pending: list):
        super().__init__(f"version {version} is signed; not adopted yet: {', '.join(pending)}")
        self.version, self.pending = version, pending


class _RemoteStamps:
    def __init__(self, public: dict):
        self.public = public


class RemoteWitness:
    """A witness reached over HTTP, with the same interface as ``Witness``."""

    admin_methods = ADMIN_METHODS

    def __init__(self, url: str, timeout: float = 5.0, *, admin_token: str | None = None):
        self.url = url.rstrip("/")
        self.timeout = timeout
        self.admin_token = admin_token  # sent with the rotation calls only
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
        headers = {"Content-Type": "application/json"}
        if method in self.admin_methods and self.admin_token is not None:
            headers["Authorization"] = f"Bearer {self.admin_token}"
        req = urllib.request.Request(f"{self.url}/v0/{method}", data=json.dumps(body).encode(),
                                     headers=headers, method="POST")
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

    def heartbeat(self, challenge: str) -> dict:
        return self._call("heartbeat", {"challenge": challenge})

    def sell_stamp(self, blinded: int) -> int:
        return int(self._call("sell_stamp", {"blinded": format(blinded, "x")}), 16)

    def charters(self) -> dict:
        return self._get("charters")

    # Rotation (SPEC §5.4): operator calls, authorised by ``admin_token``.

    def freeze(self, next_charter: dict) -> tuple[str, dict]:
        out = self._call("freeze", {"charter": next_charter})
        return out["sig"], out["snapshot"]

    def adopt(self, cid: str, version: int, snapshots: list) -> None:
        out = self._call("adopt", {"constellation": cid, "version": version, "snapshots": snapshots})
        self.cid, self.version = out["constellation"], out["version"]

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


class RemoteStandby(RemoteWitness):
    """A standby member reached over HTTP, with the interface of ``succession.Standby``."""

    admin_methods = STANDBY_ADMIN_METHODS

    def __init__(self, url: str, timeout: float = 5.0, *, admin_token: str | None = None):
        self.url = url.rstrip("/")
        self.timeout = timeout
        self.admin_token = admin_token
        self.max_response = MAX_RESPONSE
        info = self._get("info")
        self.pk, self.cid, self.version = info["pk"], info["constellation"], info["version"]
        self.stamps = None

    def __repr__(self):
        return f"RemoteStandby({self.url}, {self.pk[:8]})"

    def mirror_bind(self, req: dict) -> dict:
        return self._call("mirror", {"request": req})

    def note_release(self, sigil: str, entry: dict) -> bool:
        return self._call("note_release", {"sigil": sigil, "entry": entry})

    # Operator calls, authorised by ``admin_token``.

    def enter(self, cid: str, version: int, snapshots: list) -> None:
        out = self._call("standby", {"constellation": cid, "version": version, "snapshots": snapshots})
        self.cid, self.version = out["constellation"], out["version"]

    def succeed(self, next_charter: dict, sigs: dict | None = None) -> tuple[str, dict]:
        out = self._call("succeed", {"charter": next_charter, "sigs": sigs or {}})
        return out["sig"], out["snapshot"]

    def probe(self, urls: list) -> int:
        return self._call("probe", {"urls": list(urls)})["answered"]

    def info(self) -> dict:
        return self._get("info")


class RemoteNetwork:
    """The address book of a real network: constellation id -> witness URLs.

    Unreachable witnesses are treated like crashed ones. Charter chains are
    fetched from the witnesses and verified before use. ``committees`` maps a
    constellation id to the URLs of its current successor committee's standby
    members (SPEC §5.5).
    """

    def __init__(self, directory: dict, *, timeout: float = 5.0, registry: Registry | None = None,
                 committees: dict | None = None):
        self.registry = registry or Registry()
        self.timeout = timeout
        self.urls: dict[str, list] = {cid: list(urls) for cid, urls in directory.items()}
        self.committees: dict[str, list] = {cid: list(urls) for cid, urls in (committees or {}).items()}
        self._clients: dict[str, RemoteWitness] = {}
        self._standbys: dict[str, RemoteStandby] = {}
        self.down: set[str] = set()
        for cid in self.urls:
            self.refresh_charters(cid)

    def _standby_client(self, url: str) -> RemoteStandby | None:
        c = self._standbys.get(url)
        if c is None:
            try:
                c = self._standbys[url] = RemoteStandby(url, self.timeout)
            except Unreachable:
                return None
        return c

    def committee(self, cid: str) -> list:
        """The reachable standby members of ``cid``'s current version."""
        return [m for m in (self._standby_client(u) for u in self.committees.get(cid, []))
                if m is not None and m.pk not in self.down]

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

    def rotate(self, cid: str, new_urls: list, admin_token, *, committee_urls: list | None = None,
               dead_man: int | None = None) -> int:
        """Rotate ``cid`` to the witnesses serving at ``new_urls``; returns the new version.

        As ``Network.rotate``: every reachable current member freezes for the
        next charter and signs it, and every new member adopts the union of the
        evidence handed over by the members that signed. New members must be
        running and not yet joined (``witnessd run --adopt``). ``admin_token``
        is one token for every witness, or a dict ``{url: token}``.

        If the current version has a successor committee, its standby members get
        the members' signatures as the request and must sign too (SPEC §5.5); their
        mirror logs join the evidence. ``committee_urls`` (standby members started
        with ``witnessd standby --wait``) and ``dead_man`` give the new version a
        committee, which enters standby with the same evidence.

        Nothing a witness answers is trusted: a charter signature that does not
        verify is dropped together with its evidence. Raises ``RuntimeError`` if
        fewer than a quorum signed (the members that did sign stay frozen, as
        with ``Network.rotate``), and ``RotationIncomplete`` if the new version
        is in force but some new member or standby member has not adopted.
        """
        token = admin_token.get if isinstance(admin_token, dict) else (lambda _url: admin_token)
        chain, cur = self._current(cid)
        new = [RemoteWitness(u, self.timeout, admin_token=token(u)) for u in new_urls]
        standbys, succ = self._new_committee(committee_urls, dead_man, token)
        nxt = charter_body(cur["name"], cur["version"] + 1, [w.pk for w in new], charter_hash(cur), succ)
        sigs, snapshots = {}, []
        for url in self.urls.get(cid, []):
            try:
                w = RemoteWitness(url, self.timeout, admin_token=token(url))
                sig, snap = w.freeze(nxt)
            except Rejected:  # includes Unreachable
                continue
            if (w.pk in cur["witnesses"] and w.pk not in sigs and isinstance(sig, str)
                    and verify(w.pk, "charter", nxt, sig)):
                sigs[w.pk] = sig
                snapshots.append(snap)
        if len(sigs) < quorum(len(cur["witnesses"])):
            raise RuntimeError("not enough live witnesses to rotate")
        frozen = set(sigs)
        if cur.get("successor") is not None:
            csigs = self._committee_sign(cid, cur, nxt, dict(sigs), snapshots, token)
            if len(csigs) < quorum(len(cur["successor"]["committee"])):
                raise RuntimeError("not enough live standby members to sign the rotation")
            sigs.update(csigs)
        return self._install(cid, chain, cur, nxt, sigs, snapshots, new, frozen, standbys,
                             list(new_urls), list(committee_urls or []))

    def succeed(self, cid: str, new_urls: list, admin_token, *, committee_urls: list | None = None,
                dead_man: int | None = None) -> int:
        """Dead-man takeover of ``cid`` (SPEC §5.5); returns the new version.

        The current version's standby members sign the next charter alone, each
        only if the dead-man condition holds for it; the new members adopt from
        their mirror logs. Raises ``RuntimeError`` without a quorum of signatures.
        """
        token = admin_token.get if isinstance(admin_token, dict) else (lambda _url: admin_token)
        chain, cur = self._current(cid)
        if cur.get("successor") is None:
            raise ValueError("this version names no successor committee")
        new = [RemoteWitness(u, self.timeout, admin_token=token(u)) for u in new_urls]
        standbys, succ = self._new_committee(committee_urls, dead_man, token)
        nxt = charter_body(cur["name"], cur["version"] + 1, [w.pk for w in new], charter_hash(cur), succ)
        snapshots: list = []
        sigs = self._committee_sign(cid, cur, nxt, {}, snapshots, token)
        if len(sigs) < quorum(len(cur["successor"]["committee"])):
            raise RuntimeError("not enough standby members agree the version is dead")
        return self._install(cid, chain, cur, nxt, sigs, snapshots, new, set(), standbys,
                             list(new_urls), list(committee_urls or []))

    def probe(self, cid: str, admin_token) -> int:
        """Have every reachable standby member of ``cid`` challenge its members now."""
        token = admin_token.get if isinstance(admin_token, dict) else (lambda _url: admin_token)
        n = 0
        for url in self.committees.get(cid, []):
            try:
                n += RemoteStandby(url, self.timeout, admin_token=token(url)).probe(self.urls.get(cid, []))
            except Rejected:
                continue
        return n

    def _current(self, cid: str) -> tuple[list, dict]:
        self.refresh_charters(cid)
        chain = self.registry.chain(cid)
        if not chain:
            raise ValueError(f"unknown constellation {cid[:12]}")
        return chain, chain[-1]["body"]

    def _new_committee(self, urls, dead_man, token) -> tuple[list, dict | None]:
        if not urls:
            return [], None
        if dead_man is None:
            raise ValueError("a new committee needs a dead_man period")
        standbys = [RemoteStandby(u, self.timeout, admin_token=token(u)) for u in urls]
        return standbys, successor_clause([m.pk for m in standbys], dead_man)

    def _committee_sign(self, cid, cur, nxt, member_sigs, snapshots, token) -> dict:
        out = {}
        committee = cur["successor"]["committee"]
        for url in self.committees.get(cid, []):
            try:
                m = RemoteStandby(url, self.timeout, admin_token=token(url))
                sig, snap = m.succeed(nxt, member_sigs)
            except Rejected:  # includes Unreachable
                continue
            if (m.pk in committee and m.pk not in out and isinstance(sig, str)
                    and verify(m.pk, "charter", nxt, sig)):
                out[m.pk] = sig
                snapshots.append(snap)
        return out

    def _install(self, cid, chain, cur, nxt, sigs, snapshots, new, frozen, standbys, new_urls,
                 committee_urls) -> int:
        new_chain = chain + [{"body": nxt, "sigs": sigs}]
        self.registry.add_chain(cid, new_chain)
        # Everyone involved learns the new version (gossip admits it only if it verifies).
        everyone = self.urls.get(cid, []) + new_urls + self.committees.get(cid, []) + committee_urls
        for url in dict.fromkeys(everyone):
            try:
                RemoteWitness(url, self.timeout).gossip({"charters": {cid: new_chain}})
            except Rejected:
                pass
        pending = []
        for w in new:
            if w.pk in cur["witnesses"] and w.pk not in frozen:
                pending.append(w.url)  # a re-used key must bring its own votes (SPEC §5.4)
                continue
            try:
                w.adopt(cid, nxt["version"], snapshots)
            except Rejected:
                pending.append(w.url)
        for m in standbys:
            try:
                m.enter(cid, nxt["version"], snapshots)
            except Rejected:
                pending.append(m.url)
        for url in everyone:
            self._clients.pop(url, None)
            self._standbys.pop(url, None)
        self.urls[cid] = new_urls
        self.committees[cid] = committee_urls
        if pending:
            raise RotationIncomplete(nxt["version"], pending)
        return nxt["version"]

    def find_votes(self, sigil: str) -> list:
        out = []
        for cid in self.urls:
            for w in self.witnesses(cid):
                try:
                    out.extend(w.status(sigil)["votes"])
                except Rejected:
                    pass
        return out
