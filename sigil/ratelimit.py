"""Admission control for a witness on the open network (docs/WIRE.md "Admission control").

Stamps (``sigil.stamps``) price a witness's attention, but they are opt-in and
``/v0/sell_stamp`` blind-signs for anyone who asks, so stamps alone limit
nothing until a deployment puts a payment channel in front of them. A witness
listening on a non-loopback address therefore limits every client by default:

* a **token bucket per client** (``RateLimiter``): ``rate`` requests per second,
  bursts of up to ``burst``. The client is its IPv4 address or its IPv6 /64
  (one subscriber usually holds a whole /64). A request over the limit is
  answered HTTP 429 ``rejected`` before its body is read: the witness's state
  never sees it, so a refusal can only cost liveness, never safety (declining to
  vote is abstention, SPEC §5);
* **connection caps**: at most ``MAX_CONNECTIONS`` open connections in all and
  ``MAX_CLIENT_CONNECTIONS`` per client, and an idle connection is closed after
  ``IDLE_TIMEOUT`` seconds, so slow or silent clients cannot pin threads or
  file descriptors.

A witness listening on loopback (tests, a local testnet) has no rate limit unless
asked for one; ``--rate-limit 0`` turns it off anywhere. The Rust witness
(``rust/sigil-witness/src/ratelimit.rs``) implements the same rules with the same
defaults, bit for bit (``tests/vectors.rs`` replays this module's verdicts).
"""

import ipaddress
import math
import threading
import time
from collections import OrderedDict

DEFAULT_RATE = 20.0          # requests per second per client
DEFAULT_BURST = 100          # tokens a client may save up
MAX_CLIENTS = 65_536         # buckets kept; the least recently seen is forgotten first
MAX_CONNECTIONS = 256        # open connections in all
MAX_CLIENT_CONNECTIONS = 16  # open connections per client (with a rate limit)
IDLE_TIMEOUT = 30.0          # seconds a connection may wait for the client


def client_key(host: str) -> str:
    """The client a request is counted against: an IPv4 address or an IPv6 /64."""
    try:
        ip = ipaddress.ip_address(host)
    except ValueError:
        return host
    if ip.version == 6:
        if ip.ipv4_mapped is not None:
            return str(ip.ipv4_mapped)
        return f"{ipaddress.IPv6Network((int(ip) >> 64 << 64, 64)).network_address}/64"
    return str(ip)


def is_loopback(host: str) -> bool:
    """Does a listen address only accept connections from this machine?"""
    if host == "localhost":
        return True
    try:
        return ipaddress.ip_address(host).is_loopback
    except ValueError:
        return False


class RateLimiter:
    """A token bucket per client key.

    A full bucket holds ``burst`` tokens; it refills at ``rate`` tokens per
    second and each request takes one. Forgetting a bucket gives that client a
    full one, so evicting the least recently seen when ``max_clients`` are
    tracked can only ever favour the evicted client: an attacker with many
    addresses gains nothing it would not get from fresh addresses anyway.
    """

    def __init__(self, rate: float = DEFAULT_RATE, burst: int = DEFAULT_BURST, *,
                 clock=time.monotonic, max_clients: int = MAX_CLIENTS):
        if not rate > 0 or burst < 1:
            raise ValueError("rate must be positive and burst at least 1")
        self.rate, self.burst = float(rate), float(burst)
        self.clock = clock
        self.max_clients = max_clients
        self._buckets: OrderedDict[str, tuple[float, float]] = OrderedDict()
        self._lock = threading.Lock()

    def admit(self, key: str, now: float | None = None) -> int:
        """Take one token for ``key``. Returns 0 if admitted, else the seconds to wait."""
        with self._lock:
            now = self.clock() if now is None else now
            tokens, last = self._buckets.pop(key, (self.burst, now))
            tokens = min(self.burst, tokens + max(0.0, now - last) * self.rate)
            wait = 0
            if tokens >= 1.0:
                tokens -= 1.0
            else:
                wait = max(1, math.ceil((1.0 - tokens) / self.rate))
            self._buckets[key] = (tokens, now)
            while len(self._buckets) > self.max_clients:
                self._buckets.popitem(last=False)
            return wait

    def __len__(self) -> int:
        return len(self._buckets)


class ConnectionLimiter:
    """Counts open connections, in all and per client."""

    def __init__(self, total: int = MAX_CONNECTIONS, per_client: int | None = MAX_CLIENT_CONNECTIONS):
        self.total, self.per_client = total, per_client
        self._open: dict[str, int] = {}
        self._n = 0
        self._lock = threading.Lock()

    def acquire(self, key: str) -> bool:
        with self._lock:
            if self._n >= self.total or (self.per_client is not None and self._open.get(key, 0) >= self.per_client):
                return False
            self._n += 1
            self._open[key] = self._open.get(key, 0) + 1
            return True

    def release(self, key: str) -> None:
        with self._lock:
            self._n -= 1
            left = self._open.get(key, 1) - 1
            if left:
                self._open[key] = left
            else:
                self._open.pop(key, None)
