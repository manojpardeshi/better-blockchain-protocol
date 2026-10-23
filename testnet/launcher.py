"""A local multi-process testnet: every witness is its own ``sigil.witnessd`` process.

Layout of a testnet directory::

    keys/<name>-<i>.json, .pub   witness keys (private files are 0600)
    data/<name>-<i>.db           witness stores (durable across restarts)
    logs/<name>-<i>.log          witness stdout/stderr
    registry.json                charter registry (docs/WIRE.md)
    directory.json               network directory (docs/WIRE.md)
    testnet.json                 launcher state: one entry per witness, with port and pid

``Testnet`` is used by ``python -m testnet.up`` / ``testnet.down`` and by
``tests/test_testnet.py`` (which also kills and restarts witnesses).
"""

import json
import os
import signal
import socket
import subprocess
import sys
import time
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NAMES = ["orion", "lyra", "vega", "draco", "cygnus", "hydra", "pyxis", "lupus"]


def free_port(host: str = "127.0.0.1") -> int:
    with socket.socket() as s:
        s.bind((host, 0))
        return s.getsockname()[1]


def _env() -> dict:
    env = dict(os.environ)
    env["PYTHONPATH"] = ROOT + os.pathsep + env.get("PYTHONPATH", "") if env.get("PYTHONPATH") else ROOT
    return env


def _witnessd(*args: str) -> str:
    out = subprocess.run([sys.executable, "-m", "sigil.witnessd", *args], env=_env(), cwd=ROOT,
                         check=True, capture_output=True, text=True)
    return out.stdout.strip()


class Testnet:
    def __init__(self, directory: str, host: str = "127.0.0.1"):
        self.dir = os.path.abspath(directory)
        self.host = host
        self.state_path = os.path.join(self.dir, "testnet.json")
        self.witnesses: list[dict] = []   # {name, cid, key, store, log, port, pid}
        self.procs: dict[int, subprocess.Popen] = {}  # index -> process we started
        if os.path.exists(self.state_path):
            with open(self.state_path) as f:
                self.witnesses = json.load(f)["witnesses"]

    def path(self, *parts: str) -> str:
        return os.path.join(self.dir, *parts)

    # ------------------------------------------------------------- creation

    def create(self, constellations: int = 2, witnesses: int = 4, stamps: bool = False) -> list:
        """Generate keys and genesis charters; returns the constellation ids."""
        if self.witnesses:
            raise RuntimeError(f"{self.dir} already holds a testnet")
        for d in ("keys", "data", "logs"):
            os.makedirs(self.path(d), exist_ok=True)
        registry, cids = self.path("registry.json"), []
        for c in range(constellations):
            name = NAMES[c] if c < len(NAMES) else f"c{c}"
            keys = [self.path("keys", f"{name}-{i}.json") for i in range(witnesses)]
            for k in keys:
                _witnessd("keygen", "--out", k)
            cid = _witnessd("genesis", "--name", name, "--out", registry,
                            "--keys", *(os.path.splitext(k)[0] + ".pub" for k in keys))
            cids.append(cid)
            for i, k in enumerate(keys):
                self.witnesses.append({
                    "name": f"{name}-{i}", "cid": cid, "key": k, "stamps": stamps,
                    "store": self.path("data", f"{name}-{i}.db"), "log": self.path("logs", f"{name}-{i}.log"),
                    "port": free_port(self.host), "pid": None,
                })
        directory = {"constellations": {}}
        for w in self.witnesses:
            directory["constellations"].setdefault(w["cid"], []).append(f"http://{self.host}:{w['port']}")
        with open(self.path("directory.json"), "w") as f:
            json.dump(directory, f, indent=1)
        self._save()
        return cids

    def _save(self) -> None:
        with open(self.state_path, "w") as f:
            json.dump({"witnesses": self.witnesses}, f, indent=1)

    def directory(self) -> dict:
        """The ``{cid: [url, ...]}`` map that ``RemoteNetwork`` takes."""
        with open(self.path("directory.json")) as f:
            return json.load(f)["constellations"]

    def url(self, i: int) -> str:
        return f"http://{self.host}:{self.witnesses[i]['port']}"

    # ------------------------------------------------------------ processes

    def start(self, i: int, *, detach: bool = False) -> None:
        """Start witness ``i`` (on its fixed port and store); does not wait for it."""
        w = self.witnesses[i]
        cmd = [sys.executable, "-m", "sigil.witnessd", "run", "--key", w["key"],
               "--registry", self.path("registry.json"), "--constellation", w["cid"],
               "--store", w["store"], "--host", self.host, "--port", str(w["port"])]
        if w.get("stamps"):
            cmd.append("--stamps")
        with open(w["log"], "a") as log:
            p = subprocess.Popen(cmd, env=_env(), cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                 stdin=subprocess.DEVNULL, start_new_session=detach)
        self.procs[i] = p
        w["pid"] = p.pid
        self._save()

    def start_all(self, *, detach: bool = False, timeout: float = 30) -> None:
        for i in range(len(self.witnesses)):
            self.start(i, detach=detach)
        for i in range(len(self.witnesses)):
            self.wait_ready(i, timeout)

    def wait_ready(self, i: int, timeout: float = 30) -> None:
        deadline = time.monotonic() + timeout
        while True:
            p = self.procs.get(i)
            if p is not None and p.poll() is not None:
                raise RuntimeError(f"{self.witnesses[i]['name']} exited with {p.returncode}; "
                                   f"see {self.witnesses[i]['log']}")
            try:
                with urllib.request.urlopen(self.url(i) + "/v0/info", timeout=1) as r:
                    if json.loads(r.read())["ok"]["pk"]:
                        return
            except OSError:
                pass
            if time.monotonic() > deadline:
                raise TimeoutError(f"{self.witnesses[i]['name']} did not come up")
            time.sleep(0.05)

    def kill(self, i: int, sig: int = signal.SIGKILL, timeout: float = 10) -> None:
        """Send ``sig`` to witness ``i`` and wait for it to exit."""
        w = self.witnesses[i]
        pid = w["pid"]
        if pid is None or (i not in self.procs and not _runs(pid, w["store"])):
            w["pid"] = None  # gone, or the pid now belongs to an unrelated process
            self._save()
            return
        try:
            os.kill(pid, sig)
        except ProcessLookupError:
            pass
        p = self.procs.pop(i, None)
        if p is not None:
            try:
                p.wait(timeout)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait()
        else:  # started by another launcher process: poll until it is gone
            deadline = time.monotonic() + timeout
            while _alive(pid) and time.monotonic() < deadline:
                time.sleep(0.05)
            if _alive(pid):
                os.kill(pid, signal.SIGKILL)
        self.witnesses[i]["pid"] = None
        self._save()

    def stop_all(self, sig: int = signal.SIGTERM) -> None:
        for i in range(len(self.witnesses)):
            self.kill(i, sig)


def _runs(pid: int, store: str) -> bool:
    """Is ``pid`` a witnessd process serving ``store``? (pids get reused)"""
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as f:
            cmd = f.read().decode(errors="replace").replace("\0", " ")
    except FileNotFoundError:
        if os.path.isdir("/proc"):
            return False
        r = subprocess.run(["ps", "-o", "command=", "-p", str(pid)], capture_output=True, text=True)
        cmd = r.stdout
    except OSError:
        return False
    return "sigil.witnessd" in cmd and store in cmd


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    try:  # a zombie child of ours counts as gone
        return os.waitpid(pid, os.WNOHANG) == (0, 0)
    except ChildProcessError:
        return True
