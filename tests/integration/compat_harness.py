"""Fixtures for the soak and compatibility tests: processes, temp dirs, ports, HTTP, /proc stats.

(The end-to-end tests use ``harness.py``; both build on ``bench/common.py``.)

The witness processes are started from files written by the Python daemon (keys,
registries), exactly as ``bench/common.py`` does; ``Cluster`` and ``manual_spend`` are
re-exported from there. ``Daemon`` runs one witness or standby member of either kind
from explicit files (used where two processes must share a key, e.g. wire twins).
"""

import json
import os
import shutil
import signal
import socket
import statistics
import subprocess
import sys
import tempfile
import time
import unittest
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


from tests.integration.harness import common  # noqa: E402  (bench/common.py, loaded once)
Cluster = common.Cluster
manual_spend = common.manual_spend
RUST_BIN = common.RUST_BIN
witnessd = common.witnessd
env = common._env

KEEP = os.environ.get("SIGIL_KEEP") == "1"


def rust_available() -> bool:
    return os.path.isfile(RUST_BIN) and os.access(RUST_BIN, os.X_OK)


# Skip without the Rust binary, unless SIGIL_REQUIRE_RUST=1 (CI), where the tests then fail.
requires_rust = unittest.skipUnless(rust_available() or os.environ.get("SIGIL_REQUIRE_RUST") == "1",
                                    f"Rust witness not built ({RUST_BIN}): "
                                    "cargo build --release --locked --manifest-path rust/Cargo.toml")


def free_port(host: str = "127.0.0.1") -> int:
    with socket.socket() as s:
        s.bind((host, 0))
        return s.getsockname()[1]


def make_tmpdir(case, prefix: str) -> str:
    """A temp directory removed when the test (or class, for a class) finishes."""
    d = tempfile.mkdtemp(prefix=f"sigil-it-{prefix}-")
    if not KEEP:
        add = case.addClassCleanup if isinstance(case, type) else case.addCleanup
        add(shutil.rmtree, d, ignore_errors=True)
    return d


def du(path: str) -> int:
    """Bytes used by ``path`` (a file, or a directory recursively); 0 if missing."""
    if os.path.isfile(path):
        return os.path.getsize(path)
    total = 0
    for dirpath, _dirs, files in os.walk(path):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(dirpath, f))
            except OSError:
                pass
    return total


def store_bytes(path: str) -> int:
    """A witness store's size on disk: the redb file, or the SQLite file plus its WAL."""
    return sum(du(path + ext) for ext in ("", "-wal", "-shm"))


# ------------------------------------------------------------------ /proc

def proc_stats(pid: int) -> dict | None:
    """RSS (bytes), threads and open file descriptors of a live process (Linux /proc)."""
    try:
        with open(f"/proc/{pid}/status") as f:
            status = dict(line.split(":", 1) for line in f if ":" in line)
        fds = len(os.listdir(f"/proc/{pid}/fd"))
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return None
    return {"rss": int(status["VmRSS"].split()[0]) * 1024, "threads": int(status["Threads"]), "fds": fds}


def percentiles(xs: list, ps=(50, 95, 99)) -> dict:
    if not xs:
        return {f"p{p}": None for p in ps} | {"n": 0}
    s = sorted(xs)
    out = {f"p{p}": s[min(len(s) - 1, int(round(p / 100 * (len(s) - 1))))] for p in ps}
    out["n"] = len(s)
    out["mean"] = statistics.fmean(s)
    return out


# ------------------------------------------------------------------ HTTP

def http(url: str, path: str, body=None, *, raw: bytes | None = None, method: str | None = None,
         headers: dict | None = None, timeout: float = 10) -> tuple[int, dict | None, dict]:
    """One request; returns ``(status, parsed JSON or None, headers with lower-case names)``. Never raises on HTTP errors."""
    data = raw if raw is not None else (None if body is None else json.dumps(body).encode())
    method = method or ("GET" if data is None else "POST")
    req = urllib.request.Request(url + path, data=data, method=method,
                                 headers={"Content-Type": "application/json", **(headers or {})})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            code, text, hdrs = r.status, r.read(), {k.lower(): v for k, v in r.headers.items()}
    except urllib.error.HTTPError as e:
        code, text, hdrs = e.code, e.read(), {k.lower(): v for k, v in e.headers.items()}
    try:
        return code, json.loads(text), hdrs
    except ValueError:
        return code, None, hdrs


def wait_http(url: str, timeout: float = 30, proc: subprocess.Popen | None = None, log: str | None = None) -> None:
    deadline = time.monotonic() + timeout
    while True:
        if proc is not None and proc.poll() is not None:
            tail = open(log).read()[-2000:] if log and os.path.exists(log) else ""
            raise RuntimeError(f"process exited with {proc.returncode}: {tail}")
        try:
            with urllib.request.urlopen(url + "/v0/info", timeout=1) as r:
                if json.loads(r.read())["ok"]["pk"]:
                    return
        except OSError:
            pass
        if time.monotonic() > deadline:
            raise TimeoutError(f"{url} did not come up")
        time.sleep(0.02)


# ------------------------------------------------------------------ daemons

class Daemon:
    """One witness (``role="witness"``) or standby member (``role="standby"``) process."""

    def __init__(self, kind: str, key: str, registry: str, cid: str, store: str, log: str, *,
                 role: str = "witness", args: list | None = None, host: str = "127.0.0.1", port: int | None = None):
        self.kind, self.key, self.registry, self.cid = kind, key, registry, cid
        self.store, self.log, self.role, self.host = store, log, role, host
        self.args = list(args or [])
        self.port = port or free_port(host)
        self.proc: subprocess.Popen | None = None

    @property
    def url(self) -> str:
        return f"http://{self.host}:{self.port}"

    def command(self) -> list:
        sub = "standby" if self.role == "standby" else "run"
        common_args = [sub, "--key", self.key, "--registry", self.registry, "--constellation", self.cid,
                       "--store", self.store, "--host", self.host, "--port", str(self.port), *self.args]
        if self.kind == "rust":
            return [RUST_BIN, *common_args]
        return [sys.executable, "-m", "sigil.witnessd", *common_args]

    def start(self, wait: bool = True) -> "Daemon":
        with open(self.log, "a") as log:
            self.proc = subprocess.Popen(self.command(), env=env(), cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                         stdin=subprocess.DEVNULL)
        if wait:
            wait_http(self.url, proc=self.proc, log=self.log)
        return self

    def stop(self, sig: int = signal.SIGTERM, timeout: float = 15) -> int | None:
        p, self.proc = self.proc, None
        if p is None:
            return None
        if p.poll() is None:
            try:
                p.send_signal(sig)
            except ProcessLookupError:
                pass
        try:
            return p.wait(timeout)
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()
            raise

    @property
    def pid(self) -> int:
        return self.proc.pid


def run_cli(cmd: list, timeout: float = 30) -> subprocess.CompletedProcess:
    """Run a daemon command expected to exit on its own (bad configs); captures output."""
    return subprocess.run(cmd, env=env(), cwd=ROOT, capture_output=True, text=True, timeout=timeout,
                          stdin=subprocess.DEVNULL)


def daemon_cmd(kind: str, *args: str) -> list:
    return [RUST_BIN, *args] if kind == "rust" else [sys.executable, "-m", "sigil.witnessd", *args]


def new_constellation(d: str, name: str, n: int = 4, *, committee: int = 0, dead_man: int | None = None) -> dict:
    """Keys (and committee keys) plus a genesis charter in ``d/registry.json``."""
    os.makedirs(os.path.join(d, "keys"), exist_ok=True)
    reg = os.path.join(d, "registry.json")
    keys = [os.path.join(d, "keys", f"{name}-{i}.json") for i in range(n)]
    for k in keys:
        witnessd("keygen", "--out", k)
    ckeys = [os.path.join(d, "keys", f"{name}-k{i}.json") for i in range(committee)]
    for k in ckeys:
        witnessd("keygen", "--out", k)
    succ = ["--committee", *(k[:-5] + ".pub" for k in ckeys), "--dead-man", str(dead_man)] if ckeys else []
    cid = witnessd("genesis", "--name", name, "--out", reg, "--keys", *(k[:-5] + ".pub" for k in keys), *succ)
    return {"cid": cid, "keys": keys, "committee": ckeys, "registry": reg}


def write_token(d: str) -> tuple[str, str]:
    token = os.urandom(16).hex()
    path = os.path.join(d, "admin.token")
    with open(path, "w") as f:
        f.write(token + "\n")
    return token, path
