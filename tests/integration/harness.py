"""Fixtures for the end-to-end integration tests.

* ``Constellations`` wraps ``bench/common.py``'s ``Cluster``: keys and genesis
  charters are written by ``python -m sigil.witnessd``, then every witness and
  standby member runs as its own Rust (``sigil-witness``) or Python
  (``python -m sigil.witnessd``) process, with its own store under a temporary
  directory and a free port. Ports are checked: a witness that cannot bind,
  or a port answered by somebody else's process (other test runs may share the
  machine), is restarted on a new port.
* ``IntegrationCase`` gives each test its own constellations (torn down with
  SIGKILL, even if the test fails), a CLI runner that runs the wallet as a real
  process (``python -m sigil.cli``), and ``check_invariants``.
* Nothing waits by sleeping for another process: everything polls a condition
  with a deadline (``poll``). The only waits on the clock itself are for
  clock-defined events (an authorisation expiring, a dead-man period passing),
  and those also poll.

``check_invariants`` is called at the end of every test. Across all the wallets
the test names, with only a fresh view of the network (charters fetched from
the running witnesses, a fresh ``Verifier``):

1. every parcel a wallet holds is accepted by a fresh verifier from the wallet's
   own dossier (serialised and parsed again), and each balance is exactly the
   sum of those verified parcels;
2. per asset, the parcels still unspent at their home (no seal at the
   parcel's generation in any witness's STATUS) add up to the asset's supply;
3. no sigil is an input of two *complete* transitions (every input sealed),
   judged from the votes every running witness reports in STATUS.
"""

import importlib.util
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
import urllib.request
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def _load_bench_common():
    name = "sigil_bench_common"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, "bench", "common.py"))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


common = _load_bench_common()
Cluster, free_port, manual_spend, RUST_BIN = common.Cluster, common.free_port, common.manual_spend, common.RUST_BIN

from sigil import model, wallet_store  # noqa: E402
from sigil.charter import Registry, faults  # noqa: E402
from sigil.locks import keys_in  # noqa: E402
from sigil.proofs import verify_seal, verify_vote  # noqa: E402
from sigil.server import RemoteNetwork, RemoteWitness, Unreachable  # noqa: E402
from sigil.validate import Dossier, TrustPolicy, Verifier  # noqa: E402
from sigil.wallet import Wallet  # noqa: E402
from sigil.witness import Rejected  # noqa: E402

MIXED = ["rust", "python", "rust", "python"]


def poll(cond, timeout: float = 30.0, interval: float = 0.05, what: str = "condition"):
    """Call ``cond`` until it returns something truthy; raise ``TimeoutError`` at the deadline."""
    deadline = time.monotonic() + timeout
    while True:
        v = cond()
        if v:
            return v
        if time.monotonic() > deadline:
            raise TimeoutError(f"timed out waiting for {what}")
        time.sleep(interval)


def wait_until(t: float, what: str = "clock") -> None:
    """Poll the wall clock until ``time.time() > t`` (for clock-defined events such as expiry)."""
    poll(lambda: time.time() > t, timeout=max(5.0, t - time.time() + 10), interval=0.1, what=what)


def _env() -> dict:
    env = dict(os.environ)
    env["PYTHONPATH"] = ROOT + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    return env


class PortConflict(Exception):
    pass


class Constellations(Cluster):
    """A ``Cluster`` that checks each process it starts really answers on its own port."""

    def __init__(self, directory: str, host: str = "127.0.0.1"):
        super().__init__(directory, host)
        self.token = os.urandom(16).hex()
        self.token_file = os.path.join(self.dir, "admin.token")
        with open(self.token_file, "w") as f:
            f.write(self.token + "\n")

    def admin(self) -> dict:
        args = ["--admin-token", self.token_file]
        return {"rust": list(args), "python": list(args)}

    def expected_pk(self, i: int) -> str:
        with open(self.witnesses[i]["key"]) as f:
            return json.load(f)["pk"]

    def wait_ready(self, i: int, timeout: float = 30) -> None:
        want = self.expected_pk(i)
        deadline = time.monotonic() + timeout
        w = self.witnesses[i]
        while True:
            p = self.procs.get(i)
            if p is not None and p.poll() is not None:
                with open(w["log"], errors="replace") as f:
                    tail = f.read()[-2000:]
                if "in use" in tail.lower() or "os error 98" in tail.lower() or "errno 98" in tail.lower():
                    raise PortConflict(w["name"])
                raise RuntimeError(f"{w['name']} exited with {p.returncode}:\n{tail}")
            try:
                with urllib.request.urlopen(self.url(i) + "/v0/info", timeout=1) as r:
                    pk = json.loads(r.read())["ok"]["pk"]
                if pk == want:
                    return
                if p is None or p.poll() is not None or time.monotonic() > deadline - timeout / 2:
                    raise PortConflict(w["name"])  # somebody else's process holds the port
            except (OSError, ValueError, KeyError):
                pass
            if time.monotonic() > deadline:
                raise TimeoutError(f"{w['name']} did not come up; see {w['log']}")
            time.sleep(0.02)

    def start_all(self, only: list | None = None, new_port_ok: bool = True) -> None:
        idx = list(range(len(self.witnesses))) if only is None else list(only)
        for i in idx:
            self.start(i)
        for i in idx:
            for attempt in range(6):
                try:
                    self.wait_ready(i)
                    break
                except PortConflict:
                    if not new_port_ok or attempt == 5:
                        raise
                    self.kill(i, signal.SIGKILL)
                    self.witnesses[i]["port"] = free_port(self.host)
                    self.start(i)

    def restart(self, i: int, sig: int = signal.SIGKILL) -> None:
        """Kill a process and start it again on the same store and port."""
        self.kill(i, sig)
        self.start(i)
        self.wait_ready(i)

    def running(self, i: int) -> bool:
        p = self.procs.get(i)
        return p is not None and p.poll() is None

    def urls(self, idx) -> list:
        return [self.url(i) for i in idx]

    def constellation(self, name: str, kinds: list, *, extra: dict | None = None, committee: list | None = None,
                      dead_man: int | None = None, start: bool = True) -> tuple[str, list]:
        """Create (and start) a constellation whose witnesses accept the admin token."""
        args = self.admin()
        for k, v in (extra or {}).items():
            args[k] = args.get(k, []) + list(v)
        cid = self.create(name, kinds, args, committee=committee, dead_man=dead_man,
                          standby_args=self.admin() if committee else None)
        idx = self.indices(cid)
        if start:
            self.start_all(idx)
        return cid, idx

    def all_running_witness_urls(self) -> dict:
        """``{cid: [url, …]}`` of every running witness process (any version, frozen or not)."""
        out: dict = defaultdict(list)
        for i, w in enumerate(self.witnesses):
            if w.get("role") != "standby" and self.running(i):
                out[w["cid"]].append(self.url(i))
        return dict(out)


def require_rust() -> None:
    """Skip without the Rust witness binary (fail instead if ``SIGIL_REQUIRE_RUST=1``, as in CI)."""
    if not os.path.exists(RUST_BIN):
        msg = f"Rust witness not built ({RUST_BIN}): cargo build --release --locked --manifest-path rust/Cargo.toml"
        if os.environ.get("SIGIL_REQUIRE_RUST") == "1":
            raise RuntimeError(msg)
        raise unittest.SkipTest(msg)


class IntegrationCase(unittest.TestCase):
    """Base class: each test gets its own processes, temp dir and CLI runner."""

    @classmethod
    def setUpClass(cls):
        require_rust()

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="sigil-it-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.c = Constellations(os.path.join(self.tmp, "net"))
        self.addCleanup(self.c.stop_all, signal.SIGKILL)
        self.wallet_dirs: dict[str, str] = {}
        self.directory_file = os.path.join(self.tmp, "directory.json")
        self.t0 = time.monotonic()

    # ------------------------------------------------------------ network

    def write_directory(self, directory: dict, path: str | None = None) -> str:
        path = path or self.directory_file
        tmp = path + ".tmp"
        with open(tmp, "w") as f:
            json.dump({"constellations": directory}, f)
        os.replace(tmp, path)
        return path

    def net(self, directory: dict | None = None, **kw) -> RemoteNetwork:
        kw.setdefault("timeout", 10)
        return RemoteNetwork(directory if directory is not None else self.c.directory(), **kw)

    # ---------------------------------------------------------------- CLI

    def wpath(self, who: str) -> str:
        return self.wallet_dirs.setdefault(who, os.path.join(self.tmp, "wallets", who))

    def file(self, name: str) -> str:
        return os.path.join(self.tmp, name)

    def cli(self, who: str, *argv, ok: bool = True, directory: str | None = None, timeout: float = 120):
        """Run ``python -m sigil.cli`` as its own process; return its JSON output (stderr's if not ok)."""
        cmd = [sys.executable, "-m", "sigil.cli", "--wallet", self.wpath(who),
               "--directory", directory or self.directory_file, *map(str, argv)]
        p = subprocess.run(cmd, cwd=ROOT, env=_env(), capture_output=True, text=True, timeout=timeout)
        if ok:
            self.assertEqual(p.returncode, 0, f"{' '.join(cmd[3:])}\nstdout: {p.stdout}\nstderr: {p.stderr}")
            return json.loads(p.stdout)
        self.assertEqual(p.returncode, 1, f"{' '.join(cmd[3:])} should fail cleanly\nstdout: {p.stdout}\n"
                                          f"stderr: {p.stderr}")
        try:
            return json.loads(p.stderr)
        except ValueError:
            self.fail(f"{' '.join(cmd[3:])}: error output is not JSON (uncaught exception?):\n{p.stderr}")

    def address_file(self, who: str, **kw) -> str:
        addr = self.cli(who, "address", **kw)
        path = self.file(f"addr-{who}-{addr['salt'][:10]}.json")
        with open(path, "w") as f:
            json.dump(addr, f)
        return path

    def cli_pay(self, payer: str, payee: str, asset: str, amount: int, **kw) -> tuple[str, dict]:
        out = self.file(f"pay-{payer}-{payee}-{os.urandom(4).hex()}.json")
        r = self.cli(payer, "pay", self.address_file(payee, **kw), asset, amount, "--out", out, **kw)
        return out, r

    def cli_balance(self, who: str, asset: str, **kw) -> int:
        return self.cli(who, "balance", asset, **kw)[asset]

    def load_wallet(self, who: str, directory: dict | None = None) -> Wallet:
        """A CLI wallet loaded read-only (for invariant checks)."""
        return wallet_store.load(self.wpath(who), self.net(directory))

    # --------------------------------------------------------- invariants

    def fresh_registry(self) -> Registry:
        """Charter chains fetched from every running witness and standby member, verified."""
        reg = Registry()
        for i, w in enumerate(self.c.witnesses):
            if not self.c.running(i):
                continue
            try:
                with urllib.request.urlopen(self.c.url(i) + "/v0/charters", timeout=10) as r:
                    chains = json.loads(r.read())["ok"]
            except (OSError, ValueError, KeyError):
                continue
            for cid, chain in chains.items():
                try:
                    if len(chain) > len(reg.chain(cid)):
                        reg.add_chain(cid, chain)
                except ValueError:
                    pass
        return reg

    def _status(self, url: str, sigil: str, cache: dict) -> dict | None:
        """A witness's STATUS (None if unreachable); waits out a rate limit (polling)."""
        key = (url, sigil)
        if key not in cache:
            w = bare_client(url)
            deadline = time.monotonic() + 30
            while True:
                try:
                    got = w.status(sigil)
                    break
                except Unreachable:
                    got = None
                    break
                except Rejected as e:
                    if str(e) != "rate limited":
                        got = None
                        break
                    if time.monotonic() > deadline:
                        raise TimeoutError(f"STATUS from {url} stayed rate limited") from e
                    time.sleep(0.2)
            cache[key] = got
        return cache[key]

    def sealed_tids(self, sigil: str, home: str, gen: int | None, reg: Registry, cache: dict) -> set:
        """``(gen, tid)`` pairs a quorum of some charter version of ``home`` voted for ``sigil``."""
        groups: dict[tuple, dict] = defaultdict(dict)
        for url in self.c.all_running_witness_urls().get(home, []):
            st = self._status(url, sigil, cache)
            for v in (st or {}).get("votes", []):
                if (v.get("sigil") == sigil and v.get("constellation") == home and verify_vote(v)
                        and (gen is None or v["gen"] == gen)):
                    groups[(v["version"], v["gen"], v["tid"])][v["witness"]] = v
        out = set()
        for (_version, g, tid), vs in groups.items():
            if verify_seal(model.seal_from_votes(list(vs.values())), reg):
                out.add((g, tid))
        return out

    def check_invariants(self, wallets: dict, *, headers=(), supply: dict | None = None,
                         stale: dict | None = None) -> dict:
        """Check the end-state invariants (module docstring) over ``wallets`` ({name: Wallet}).

        ``headers`` are extra transition headers the test made outside any wallet
        (manual spends). ``stale`` maps a wallet name to how many of its holdings the
        test expects to be spent behind its back (a cheater's). Returns per-asset totals.
        """
        reg = self.fresh_registry()
        cache: dict = {}
        live_totals: dict[str, int] = defaultdict(int)
        supplies: dict[str, int] = {}
        known: dict[str, dict] = {}       # tid -> header
        parcels: dict[str, dict] = {}     # sigil -> parcel
        for name, w in wallets.items():
            # 1. A fresh verifier, from the wallet's own dossier as stored.
            dossier = Dossier.from_json(w.dossier.to_json())
            policy = TrustPolicy(Registry(), w.policy.trusted)
            policy.convicted = set(w.policy.convicted)
            for cid in reg.ids():           # charters known to the network (rotations included)
                policy.registry.add_chain(cid, reg.chain(cid))
            fresh = Verifier(policy)
            mine: dict[str, int] = defaultdict(int)
            n_stale = 0
            for pid, h in w.holdings.items():
                p = fresh.verify_parcel(dossier, h["ref"])
                self.assertEqual(p, h["parcel"], f"{name}: holding differs from its dossier")
                self.assertEqual(model.parcel_id(h["ref"]), pid)
                self.assertTrue(policy.trusts(p["home"]), f"{name} holds a parcel in an untrusted home")
                if not keys_in(p["lock"]) & set(w.keys):
                    continue
                mine[p["asset"]] += p["amount"]
                # 2. Unspent at its home: no seal at its current generation.
                if self.sealed_tids(h["sigil"], p["home"], h["gen"], reg, cache):
                    n_stale += 1
                else:
                    live_totals[p["asset"]] += p["amount"]
            for asset, amount in mine.items():
                self.assertEqual(w.balance(asset), amount, f"{name}: balance of {asset[:12]} not backed")
            self.assertEqual(n_stale, (stale or {}).get(name, 0), f"{name}: holdings spent behind its back")
            for tid, tx in w.dossier.transitions.items():
                known[tid] = tx["header"]
                g = tx["body"].get("genesis")
                if g:
                    supplies[tid] = g["supply"]
                for o in tx["body"]["outputs"]:
                    parcels[model.sigil_of(o)] = o
            for tid, pend in w.pending.items():
                known[tid] = pend["header"]
        for h in headers:
            known[model.transition_id(h)] = h
        # 2. Conservation of every asset issued in these wallets' histories.
        for asset, total in (supply or supplies).items():
            self.assertEqual(live_totals.get(asset, 0), total, f"supply of {asset[:12]} not conserved")
        # 3. No sigil consumed by two complete transitions.
        complete_cache: dict[str, bool] = {}

        def complete(tid: str) -> bool:
            if tid not in complete_cache:
                hd = known.get(tid)
                if hd is None:
                    complete_cache[tid] = True  # unknown transition: assume the worst
                else:
                    complete_cache[tid] = all(
                        s in parcels and (g, tid) in self.sealed_tids(s, parcels[s]["home"], g, reg, cache)
                        for s, g in hd["inputs"])
            return complete_cache[tid]

        inputs = {s for hd in known.values() for s, _g in hd["inputs"]}
        for s in inputs:
            if s not in parcels:
                continue
            sealed = self.sealed_tids(s, parcels[s]["home"], None, reg, cache)
            done = {tid for _g, tid in sealed if complete(tid)}
            self.assertLessEqual(len(done), 1, f"sigil {s[:12]} consumed by {len(done)} complete transitions")
        return dict(live_totals)


def bare_client(url: str, timeout: float = 10) -> RemoteWitness:
    """A ``RemoteWitness`` that skips the /v0/info call (so it works while rate limited)."""
    w = RemoteWitness.__new__(RemoteWitness)
    w.url, w.timeout, w.admin_token, w.max_response = url.rstrip("/"), timeout, None, 16 << 20
    return w
