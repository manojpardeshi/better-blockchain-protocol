"""Shared helpers for the interop test and the benchmarks.

* ``Cluster`` creates witness keys and genesis charters with the *Python* daemon
  (``python -m sigil.witnessd keygen/genesis``), so the Rust witness is always started from
  files in the reference's formats, then runs each witness as a Rust (``sigil-witness run``)
  or Python (``python -m sigil.witnessd run``) process.
* ``compat_wallet_class`` returns a ``Wallet`` that signs owner authorisations in the
  ``unlock_message = {sigil, tid, expires}`` format (SPEC §5.1 as of 4f52887). The stock
  wallet is used unchanged if it already does; otherwise ``authorise`` is overridden with an
  equivalent that passes ``expires`` to the 4-argument ``locks.sign_unlock``.
"""

import inspect
import json
import os
import signal
import socket
import subprocess
import sys
import time
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from sigil import locks, model  # noqa: E402
from sigil.locks import keys_in  # noqa: E402
from sigil.wallet import Wallet  # noqa: E402

RUST_BIN = os.environ.get("SIGIL_WITNESS_BIN", os.path.join(ROOT, "rust", "target", "release", "sigil-witness"))
AUTH_TTL = 600  # seconds an owner authorisation may newly bind a sigil


def free_port(host: str = "127.0.0.1") -> int:
    with socket.socket() as s:
        s.bind((host, 0))
        return s.getsockname()[1]


def _env() -> dict:
    env = dict(os.environ)
    env["PYTHONPATH"] = ROOT + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    return env


def witnessd(*args: str) -> str:
    out = subprocess.run([sys.executable, "-m", "sigil.witnessd", *args], env=_env(), cwd=ROOT,
                         check=True, capture_output=True, text=True)
    return out.stdout.strip()


# ------------------------------------------------------------------ wallet

def stock_wallet_signs_expiry() -> bool:
    """Does ``Wallet.authorise`` already produce expires-format unlocks?"""
    src = inspect.getsource(Wallet.authorise)
    return "expires" in src


def unlock_for(keys: list, sigil: str, tid: str, expires: int) -> dict:
    u = locks.empty_unlock(expires)
    for kp in keys:
        u["sigs"][kp.pk] = locks.sign_unlock(kp, sigil, tid, expires)
    return u


class CompatWallet(Wallet):
    """``Wallet`` whose ``authorise`` signs ``{sigil, tid, expires}`` (same guard as the stock one)."""

    def authorise(self, header: dict, body: dict, extra: dict | None = None) -> dict:
        tid = model.transition_id(header)
        expires = int(self.network.clock()) + AUTH_TTL if hasattr(self.network, "clock") else int(time.time()) + AUTH_TTL
        unlocks = {}
        for r, (s, g) in zip(body["inputs"], header["inputs"]):
            h = self.holdings.get(model.parcel_id(r))
            if h is None:
                continue
            prior = self.pledged.get(s)
            if prior is not None and prior[0] == g and prior[1] != tid:
                raise ValueError("refusing to equivocate: sigil already pledged")
            u = unlock_for([self.keys[pk] for pk in keys_in(h["parcel"]["lock"]) & set(self.keys)], s, tid, expires)
            unlocks[s] = locks.merge_unlocks(u, (extra or {}).get(s, {}))
            self.pledged[s] = (g, tid)
        return unlocks


def compat_wallet_class():
    return Wallet if stock_wallet_signs_expiry() else CompatWallet


def manual_spend(wallet, refs: list, outputs: list, memo: str = "", expires: int | None = None):
    """Build and sign a transition *without* the wallet's anti-equivocation guard."""
    header, body, tid = wallet.prepare(refs, outputs, memo)
    expires = int(time.time()) + AUTH_TTL if expires is None else expires
    unlocks, reqs = {}, []
    for r, (s, _) in zip(refs, header["inputs"]):
        p = wallet.dossier.output(r)
        unlocks[s] = unlock_for([wallet.keys[pk] for pk in keys_in(p["lock"]) & set(wallet.keys)], s, tid, expires)
        reqs.append({"sigil": s, "header": header, "home": p["home"], "lock": p["lock"],
                     "salt": p["salt"], "unlock": unlocks[s]})
    return header, body, unlocks, reqs


# ------------------------------------------------------------------ cluster

class Cluster:
    """Constellations of witness processes; each witness is ``"rust"`` or ``"python"``."""

    def __init__(self, directory: str, host: str = "127.0.0.1", wrap: list | None = None):
        self.dir = os.path.abspath(directory)
        self.host = host
        self.wrap = list(wrap or [])   # e.g. ["taskset", "-c", "0"] to pin every witness
        self.witnesses: list[dict] = []
        self.procs: dict[int, subprocess.Popen] = {}
        for d in ("keys", "data", "logs"):
            os.makedirs(os.path.join(self.dir, d), exist_ok=True)
        self.registry = os.path.join(self.dir, "registry.json")

    def create(self, name: str, kinds: list, extra_args: dict | None = None) -> str:
        keys = [os.path.join(self.dir, "keys", f"{name}-{i}.json") for i in range(len(kinds))]
        for k in keys:
            witnessd("keygen", "--out", k)
        cid = witnessd("genesis", "--name", name, "--out", self.registry,
                       "--keys", *(os.path.splitext(k)[0] + ".pub" for k in keys))
        for i, (k, kind) in enumerate(zip(keys, kinds)):
            ext = "redb" if kind == "rust" else "db"
            self.witnesses.append({
                "name": f"{name}-{i}", "cid": cid, "key": k, "kind": kind,
                "store": os.path.join(self.dir, "data", f"{name}-{i}.{ext}"),
                "log": os.path.join(self.dir, "logs", f"{name}-{i}.log"),
                "port": free_port(self.host), "args": list((extra_args or {}).get(kind, [])),
            })
        return cid

    def directory(self) -> dict:
        out: dict = {}
        for w in self.witnesses:
            out.setdefault(w["cid"], []).append(self.url(self.witnesses.index(w)))
        return out

    def url(self, i: int) -> str:
        return f"http://{self.host}:{self.witnesses[i]['port']}"

    def command(self, i: int) -> list:
        w = self.witnesses[i]
        common = ["run", "--key", w["key"], "--registry", self.registry, "--constellation", w["cid"],
                  "--store", w["store"], "--host", self.host, "--port", str(w["port"])]
        if w["kind"] == "rust":
            return [*self.wrap, RUST_BIN, *common, *w["args"]]
        return [*self.wrap, sys.executable, "-m", "sigil.witnessd", *common, *w["args"]]

    def start(self, i: int) -> None:
        with open(self.witnesses[i]["log"], "a") as log:
            self.procs[i] = subprocess.Popen(self.command(i), env=_env(), cwd=ROOT, stdout=log,
                                             stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)

    def wait_ready(self, i: int, timeout: float = 30) -> None:
        deadline = time.monotonic() + timeout
        while True:
            p = self.procs.get(i)
            if p is not None and p.poll() is not None:
                raise RuntimeError(f"{self.witnesses[i]['name']} exited with {p.returncode}; see {self.witnesses[i]['log']}")
            try:
                with urllib.request.urlopen(self.url(i) + "/v0/info", timeout=1) as r:
                    if json.loads(r.read())["ok"]["pk"]:
                        return
            except OSError:
                pass
            if time.monotonic() > deadline:
                raise TimeoutError(f"{self.witnesses[i]['name']} did not come up")
            time.sleep(0.02)

    def start_all(self) -> None:
        for i in range(len(self.witnesses)):
            self.start(i)
        for i in range(len(self.witnesses)):
            self.wait_ready(i)

    def kill(self, i: int, sig: int = signal.SIGKILL) -> None:
        p = self.procs.pop(i, None)
        if p is None:
            return
        try:
            p.send_signal(sig)
        except ProcessLookupError:
            pass
        try:
            p.wait(10)
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()

    def stop_all(self, sig: int = signal.SIGTERM) -> None:
        for i in list(self.procs):
            self.kill(i, sig)

    def pid(self, i: int) -> int:
        return self.procs[i].pid
