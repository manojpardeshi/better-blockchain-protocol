"""Witness, standby and Byzantine processes behind fault proxies, with crash, clock and disk faults.

``ChaosCluster`` extends ``bench/common.Cluster`` (keys and charters made by the Python
daemon, each process a ``sigil-witness`` or ``python -m sigil.witnessd``) with:

* a ``FaultProxy`` in front of every process for wallets and operators (``url``), and a
  second one in front of every witness for the standby members' heartbeat probes
  (``probe_url``), so standby members and witnesses can be partitioned apart while wallets
  still reach both;
* process kinds beyond ``rust`` and ``python``: ``byz:<modes>`` (``byzantine.py``) and
  ``mutant:<name>`` (``mutant.py``);
* a per-process wall-clock offset (``set_skew``) through the ``skewclock.c`` LD_PRELOAD shim;
* SIGKILL at any moment, from the harness or from a proxy kill hook, and restart on the same
  store and port;
* disk-full episodes: the store on its own tiny tmpfs that is filled up (root only), or else
  RLIMIT_FSIZE pinned to the store's current size so no file can grow.
"""

import os
import random
import shutil
import signal
import subprocess
import sys
import threading
import time
import urllib.request

from .proxy import FaultProxy

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(ROOT, "bench"))
from common import RUST_BIN, Cluster, free_port  # noqa: E402

TOKEN = "chaos-admin-token"


def build_skew_shim(out_dir: str) -> str | None:
    """Compile ``skewclock.c`` into ``out_dir``; None if no C compiler works."""
    so = os.path.join(out_dir, "skewclock.so")
    for cc in ("cc", "gcc", "clang"):
        if shutil.which(cc) is None:
            continue
        r = subprocess.run([cc, "-shared", "-fPIC", "-O2", "-o", so, os.path.join(HERE, "skewclock.c"), "-ldl"],
                           capture_output=True)
        if r.returncode == 0:
            return so
    return None


def tmpfs_available(probe_dir: str) -> bool:
    """Can we mount a tmpfs (root, CAP_SYS_ADMIN)? Leaves nothing mounted."""
    if os.geteuid() != 0 or shutil.which("mount") is None:
        return False
    os.makedirs(probe_dir, exist_ok=True)
    r = subprocess.run(["mount", "-t", "tmpfs", "-o", "size=64k", "chaos-probe", probe_dir], capture_output=True)
    if r.returncode != 0:
        return False
    subprocess.run(["umount", "-l", probe_dir], capture_output=True)
    return True


class ChaosCluster(Cluster):
    def __init__(self, directory: str, observer, seed: int, *, skew_so: str | None, client_timeout: float):
        super().__init__(directory)
        self.observer = observer
        self.rng = random.Random(seed ^ 0x5EED)
        self.seed = seed
        self.skew_so = skew_so
        self.client_timeout = client_timeout
        self.proxies: dict[int, FaultProxy] = {}
        self.probes: dict[int, FaultProxy] = {}
        self.skew: dict[int, int] = {}
        self.max_abs_skew: dict[int, int] = {}
        self.lock = threading.RLock()
        self.down: set[int] = set()        # killed and not (yet) restarted
        self.retired: set[int] = set()     # never restarted by the chaos thread again
        self.mounts: list[str] = []
        self.disk_full: dict[int, str] = {}  # i -> "tmpfs" | "fsize"
        self.kills = 0
        self.token_file = os.path.join(self.dir, "admin.token")
        with open(self.token_file, "w") as f:
            f.write(TOKEN + "\n")
        os.makedirs(os.path.join(self.dir, "skew"), exist_ok=True)

    # ------------------------------------------------------------ addressing

    def _taken(self) -> set:
        return {w["port"] for w in self.witnesses} | {p.port for p in self.all_proxies()}

    def _fix_ports(self) -> None:
        """``free_port`` only says a port is free *now*: a later proxy, or a process that is down
        at the moment, may hold it. Give every process a port no other process or proxy uses."""
        with self.lock:
            used = {p.port for p in self.all_proxies()}
            for w in self.witnesses:
                while w["port"] in used:
                    w["port"] = free_port(self.host)
                used.add(w["port"])

    def create(self, *a, **kw):
        cid = super().create(*a, **kw)
        self._fix_ports()
        return cid

    def add_members(self, *a, **kw):
        out = super().add_members(*a, **kw)
        self._fix_ports()
        return out

    def add_standbys(self, *a, **kw):
        out = super().add_standbys(*a, **kw)
        self._fix_ports()
        return out

    def _new_proxy(self, name: str, i: int, seed: int) -> FaultProxy:
        while True:
            p = FaultProxy(name, (self.host, self.witnesses[i]["port"]), self.observer, seed,
                           client_timeout=self.client_timeout)
            if p.port not in self._taken():
                return p
            p.stop()

    def _ensure_proxies(self, i: int) -> None:
        with self.lock:
            if i in self.proxies:
                return
            w = self.witnesses[i]
            self.proxies[i] = self._new_proxy(w["name"], i, self.seed * 1009 + i)
            if w.get("role") != "standby":
                self.probes[i] = self._new_proxy(w["name"] + "/probe", i, self.seed * 2003 + i)

    def url(self, i: int) -> str:
        self._ensure_proxies(i)
        return self.proxies[i].url

    def probe_url(self, i: int) -> str:
        self._ensure_proxies(i)
        return self.probes[i].url

    def real_url(self, i: int) -> str:
        return f"http://{self.host}:{self.witnesses[i]['port']}"

    def all_proxies(self) -> list:
        return list(self.proxies.values()) + list(self.probes.values())

    # ------------------------------------------------------------ processes

    def command(self, i: int) -> list:
        w = self.witnesses[i]
        kind = w["kind"]
        common = ["standby" if w.get("role") == "standby" else "run", "--key", w["key"], "--registry", self.registry,
                  "--constellation", w["cid"], "--store", w["store"], "--host", self.host,
                  "--port", str(w["port"]), "--admin-token", self.token_file]
        if kind == "rust":
            return [RUST_BIN, *common, *w["args"]]
        if kind == "python":
            return [sys.executable, "-m", "sigil.witnessd", *common, *w["args"]]
        if kind.startswith("mutant:"):
            return [sys.executable, "-m", "tests.integration.chaos.mutant", kind.split(":", 1)[1], *common, *w["args"]]
        if kind.startswith("byz:"):
            return [sys.executable, "-m", "tests.integration.chaos.byzantine", *common[1:],
                    "--modes", kind.split(":", 1)[1], "--seed", str(self.seed * 31 + i),
                    "--oversize", str(8 << 20)]
        raise ValueError(kind)

    def _skew_file(self, i: int) -> str:
        return os.path.join(self.dir, "skew", self.witnesses[i]["name"])

    def start(self, i: int) -> None:
        self._ensure_proxies(i)
        env = dict(os.environ)
        env["PYTHONPATH"] = ROOT + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
        if self.skew_so is not None:
            path = self._skew_file(i)
            if not os.path.exists(path):
                with open(path, "w") as f:
                    f.write("0\n")
            env["LD_PRELOAD"] = self.skew_so
            env["SIGIL_SKEW_FILE"] = path
        w = self.witnesses[i]
        with open(w["log"], "a") as log:
            log.write(f"--- start {time.strftime('%H:%M:%S')}\n")
            log.flush()
            self.procs[i] = subprocess.Popen(self.command(i), env=env, cwd=ROOT, stdout=log,
                                             stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        with self.lock:
            self.down.discard(i)

    def wait_ready(self, i: int, timeout: float = 30) -> None:
        deadline = time.monotonic() + timeout
        while True:
            p = self.procs.get(i)
            if p is not None and p.poll() is not None:
                raise RuntimeError(f"{self.witnesses[i]['name']} exited with {p.returncode}; see {self.witnesses[i]['log']}")
            try:
                with urllib.request.urlopen(self.real_url(i) + "/v0/info", timeout=1) as r:
                    r.read()
                    return
            except OSError:
                pass
            if time.monotonic() > deadline:
                raise TimeoutError(f"{self.witnesses[i]['name']} did not come up")
            time.sleep(0.02)

    def alive(self, i: int) -> bool:
        p = self.procs.get(i)
        return p is not None and p.poll() is None

    def kill(self, i: int, sig: int = signal.SIGKILL) -> None:
        with self.lock:
            super().kill(i, sig)
            self.down.add(i)
            self.kills += 1

    def restart(self, i: int, wait: bool = True) -> bool:
        """Start ``i`` again on its store and port (after a crash); False if it would not come up."""
        with self.lock:
            if self.alive(i):
                return True
            self.procs.pop(i, None)
            if i in self.disk_full and self.disk_full[i] == "fsize":
                del self.disk_full[i]   # the limit belonged to the dead process
            self.start(i)
        if not wait:
            return True
        try:
            self.wait_ready(i)
            return True
        except (RuntimeError, TimeoutError):
            return False

    def crashed_on_its_own(self) -> list:
        """Processes that exited although nobody killed them (e.g. a store write failed)."""
        return [i for i, p in list(self.procs.items()) if p.poll() is not None and i not in self.down]

    # ------------------------------------------------------------ clocks

    def set_skew(self, i: int, seconds: int) -> None:
        if self.skew_so is None:
            return
        with open(self._skew_file(i) + ".tmp", "w") as f:
            f.write(f"{int(seconds)}\n")
        os.replace(self._skew_file(i) + ".tmp", self._skew_file(i))
        self.skew[i] = int(seconds)
        self.max_abs_skew[i] = max(self.max_abs_skew.get(i, 0), abs(int(seconds)))

    # ------------------------------------------------------------ disks

    def put_on_tmpfs(self, i: int, size_kib: int) -> bool:
        """Before the first start: give ``i``'s store its own ``size_kib`` tmpfs."""
        w = self.witnesses[i]
        mnt = os.path.join(self.dir, "tmpfs", w["name"])
        os.makedirs(mnt, exist_ok=True)
        r = subprocess.run(["mount", "-t", "tmpfs", "-o", f"size={size_kib}k", "chaos-" + w["name"], mnt],
                           capture_output=True)
        if r.returncode != 0:
            return False
        self.mounts.append(mnt)
        w["store"] = os.path.join(mnt, os.path.basename(w["store"]))
        w["tmpfs"] = mnt
        return True

    def fill_disk(self, i: int) -> str | None:
        """Make ``i``'s store unable to grow; returns the mechanism used, None if impossible."""
        w = self.witnesses[i]
        if w.get("tmpfs"):
            filler = os.path.join(w["tmpfs"], "filler")
            try:
                with open(filler, "ab") as f:
                    chunk = b"\0" * 4096
                    while True:
                        f.write(chunk)
                        f.flush()
            except OSError:
                pass
            self.disk_full[i] = "tmpfs"
            return "tmpfs"
        p = self.procs.get(i)
        if p is None or p.poll() is not None or shutil.which("prlimit") is None:
            return None
        size = max(os.path.getsize(f) for f in self._store_files(i))
        r = subprocess.run(["prlimit", f"--pid={p.pid}", f"--fsize={size}"], capture_output=True)
        if r.returncode != 0:
            return None
        self.disk_full[i] = "fsize"
        return "fsize"

    def _store_files(self, i: int) -> list:
        s = self.witnesses[i]["store"]
        return [f for f in (s, s + "-wal", s + "-shm", s + "-journal") if os.path.exists(f)] or [s]

    def free_disk(self, i: int) -> None:
        how = self.disk_full.pop(i, None)
        w = self.witnesses[i]
        if how == "tmpfs":
            try:
                os.remove(os.path.join(w["tmpfs"], "filler"))
            except FileNotFoundError:
                pass
        elif how == "fsize":
            p = self.procs.get(i)
            if p is not None and p.poll() is None:
                subprocess.run(["prlimit", f"--pid={p.pid}", "--fsize=unlimited"], capture_output=True)

    # ------------------------------------------------------------ teardown

    def teardown(self) -> None:
        for p in self.all_proxies():
            try:
                p.stop()
            except OSError:
                pass
        for i in list(self.procs):
            try:
                Cluster.kill(self, i, signal.SIGKILL)
            except OSError:
                pass
        for m in self.mounts:
            subprocess.run(["umount", "-l", m], capture_output=True)
