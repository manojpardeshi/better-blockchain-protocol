"""Soak: a multi-process network under a realistic mix of traffic, with resource bounds over time.

Network (every witness and standby member is its own process):

* ``orion``: 4 Rust witnesses (never rotated; long-lived, watched for leaks);
* ``lyra``: 4 Python witnesses (never rotated; long-lived, watched for leaks);
* ``vega``: 2 Rust + 2 Python witnesses, **rotated** every ``SIGIL_SOAK_ROTATE`` seconds
  (to 4 Rust, 4 Python, mixed, ... new keys each time; the frozen members are then stopped);
* ``heir``: 2 Rust + 2 Python witnesses with a successor committee of 2 Rust + 2 Python
  standby members probing them; once, mid-run, the members are killed and the committee
  **succeeds** them (dead-man takeover) with new mixed members and a new committee.

Six wallets (homes spread over the four constellations) plus occasional fresh holders run a
mix of payments within and across constellations, atomic swaps across constellations,
consolidations (many inputs, one output), wallet saves and reloads. A prober process hits
``/v0/info`` and ``/v0/status`` on random witnesses. Every ``SIGIL_SOAK_SERIES`` seconds the
issuers start a new series of their assets and payments move to it (holders do not pass one
coin's whole history around forever; within a series the dossier grows, and is measured).

Recorded every ``SIGIL_SOAK_SAMPLE`` seconds: per process RSS, threads, open fds, store and
log size; the wallets' directory sizes; the run directory's disk use; operation latencies;
STATUS latency; per hop the dossier's transitions and bytes and the time to seal, pack and
verify it. Asserted at the end (bounds are deliberately loose for shared CI machines):

* no operation failed, and value is conserved per asset at every sample;
* long-lived witnesses: open fds and threads stay bounded; RSS growth after warm-up is
  explained by the data they store (<= 64 MiB + 3x their store growth);
* store growth per sealed operation is bounded and not super-linear (second half <= 2x the
  first half + 4 KiB per op); witness logs do not grow with traffic;
* no slowdown on the witness side: STATUS and seal latency p50 in the last window <= 3x the
  first window (+ a small absolute slack);
* dossier bytes per transition stay bounded (no per-hop bloat), and a fresh holder's
  verification time per transition stays bounded.

``SIGIL_SOAK_OUT=path.json`` writes every number.
"""

import json
import os
import random
import signal
import subprocess
import sys
import time
import traceback
import unittest

from sigil import Wallet, model, wallet_store
from sigil.server import RemoteNetwork
from sigil.swap import atomic_swap
from sigil.validate import Dossier

from tests.integration.compat_harness import (Cluster, du, http, make_tmpdir, percentiles, proc_stats, requires_rust,
                                       store_bytes, write_token)

ENV = os.environ.get
DURATION = float(ENV("SIGIL_SOAK_SECONDS", "180"))
SAMPLE = float(ENV("SIGIL_SOAK_SAMPLE", "10"))
ROTATE = float(ENV("SIGIL_SOAK_ROTATE", "60"))
SERIES = float(ENV("SIGIL_SOAK_SERIES", "120"))
SUCCESSION_AT = float(ENV("SIGIL_SOAK_SUCCESSION_AT", "0.5"))   # fraction of the run; <0 disables
MAX_DISK = int(ENV("SIGIL_SOAK_MAX_DISK", str(4 << 30)))
SEED = int(ENV("SIGIL_SOAK_SEED", "1"))
DEAD_MAN = 3
MIB = 1 << 20


def log(msg: str) -> None:
    if ENV("SIGIL_SOAK_VERBOSE", "1") == "1":
        print(f"[soak {time.strftime('%H:%M:%S')}] {msg}", file=sys.stderr, flush=True)


class Soak:
    def __init__(self, case: unittest.TestCase):
        self.case = case
        self.rng = random.Random(SEED)
        self.dir = make_tmpdir(case, "soak")
        self.token, self.tfile = write_token(self.dir)
        self.c = Cluster(self.dir)
        case.addCleanup(self.c.stop_all, signal.SIGKILL)
        self.admin = {"rust": ["--admin-token", self.tfile], "python": ["--admin-token", self.tfile]}
        self.samples: list = []
        self.hops: list = []
        self.ops: list = []          # (t, kind, seconds)
        self.status_lat: list = []   # (t, seconds, kind), from the prober process
        self.errors: list = []
        self.events: list = []
        self.sealed: dict = {}       # cid -> transitions sealed with an input there
        self.down: set = set()       # constellations temporarily dead (succession window)
        self.rot_cycle = [["rust"] * 4, ["python"] * 4, ["rust", "python", "python", "rust"]]
        self.supply: dict = {}
        self.fresh: dict = {}        # asset -> units held by fresh holders (dropped after receiving)
        self.fresh_count = 0

    # ------------------------------------------------------------ setup

    def build(self):
        c = self.c
        self.R = c.create("orion", ["rust"] * 4)
        self.P = c.create("lyra", ["python"] * 4)
        self.M = c.create("vega", ["rust", "python", "rust", "python"], self.admin)
        self.H = c.create("heir", ["rust", "python", "rust", "python"], self.admin,
                          committee=["rust", "python", "rust", "python"], dead_man=DEAD_MAN)
        members = [c.url(i) for i in c.indices(self.H)]
        for i in c.indices(self.H, role="standby"):
            c.witnesses[i]["args"] += [*self.admin["rust"], "--members", *members, "--probe-every", "0.5"]
        c.start_all()
        self.long_lived = {c.witnesses[i]["name"]: i for i in c.indices(self.R) + c.indices(self.P)}
        self.net = RemoteNetwork(c.directory(), committees=c.committees(), timeout=10)
        n = self.net
        self.wallets = {
            "alice": Wallet("alice", n, self.R), "bob": Wallet("bob", n, self.R),
            "carol": Wallet("carol", n, self.P, deep_threshold=500), "dave": Wallet("dave", n, self.P),
            "erin": Wallet("erin", n, self.M), "frank": Wallet("frank", n, self.H),
        }
        self.issuers = {"USD": "alice", "GOLD": "carol", "EUR": "erin"}
        self.series = 0
        self.new_series()

    def new_series(self):
        """Each issuer issues a fresh series of its asset and hands some to everyone."""
        self.assets = {}
        for name, issuer in self.issuers.items():
            w = self.wallets[issuer]
            supply = 10_000_000
            a = w.issue(f"{name}-{self.series}", supply)
            self.supply[a] = supply
            self.assets[name] = a
            for other in self.wallets.values():
                if other is not w and other.home not in self.down:
                    self.pay(w, other, a, 50_000, record=False)
        self.series_started = time.monotonic()
        self.events.append((self.t(), "series", self.series))
        self.series += 1

    # ------------------------------------------------------------ operations

    def t(self) -> float:
        return round(time.monotonic() - self.t0, 3)

    def pay(self, src: Wallet, dst: Wallet, asset: str, amount: int, record: bool = True, kind: str = "pay"):
        addr = dst.address()
        refs, outputs = src.payment_outputs(asset, amount, addr)
        t0 = time.perf_counter()
        tid = src.transact(refs, outputs)
        t1 = time.perf_counter()
        blob = src.dossier.ancestry([tid]).to_json()
        t2 = time.perf_counter()
        before = len(dst.verifier._ok)
        d = Dossier.from_json(blob)
        dst.receive(d, [model.ref(tid, 0)])
        t3 = time.perf_counter()
        for r in refs:
            cid = src.dossier.output(r)["home"]
            self.sealed[cid] = self.sealed.get(cid, 0) + 1
        if record:
            self.hops.append({"t": self.t(), "kind": kind, "ntx": len(d), "bytes": len(blob), "seal": t1 - t0,
                              "pack": t2 - t1, "verify": t3 - t2, "new": len(dst.verifier._ok) - before,
                              "series_age": round(time.monotonic() - self.series_started, 1)})
            self.ops.append((self.t(), kind, t3 - t0))
        return tid

    def holders(self) -> list:
        return [w for w in self.wallets.values() if w.home not in self.down]

    def funded(self, w: Wallet, asset: str, amount: int) -> bool:
        return sum(h["parcel"]["amount"] for h in w.holdings.values()
                   if h["parcel"]["asset"] == asset and h["sigil"] not in w.pledged and h["parcel"]["lock"]["op"] == "sig") >= amount

    def op_pay(self, cross: bool):
        ws = self.holders()
        src = self.rng.choice(ws)
        same = [w for w in ws if w is not src and w.home == src.home]
        other = [w for w in ws if w is not src and w.home != src.home]
        pool = other if (cross or not same) else same
        if not pool:
            return
        dst = self.rng.choice(pool)
        asset = self.assets[self.rng.choice(list(self.assets))]
        amount = self.rng.randint(1, 40)
        if self.funded(src, asset, amount):
            self.pay(src, dst, asset, amount, kind="cross" if src.home != dst.home else "pay")

    def op_swap(self):
        ws = self.holders()
        a, b = self.rng.sample(ws, 2)
        x, y = self.rng.sample(list(self.assets.values()), 2)
        if self.funded(a, x, 10) and self.funded(b, y, 10):
            t0 = time.perf_counter()
            atomic_swap(a, x, self.rng.randint(1, 10), b, y, self.rng.randint(1, 10))
            self.ops.append((self.t(), "swap", time.perf_counter() - t0))
            for cid in {a.home, b.home}:
                self.sealed[cid] = self.sealed.get(cid, 0) + 2

    def op_consolidate(self):
        w = self.rng.choice(self.holders())
        for asset in self.assets.values():
            hs = [h for h in w.holdings.values() if h["parcel"]["asset"] == asset and h["sigil"] not in w.pledged
                  and h["parcel"]["lock"]["op"] == "sig"]
            if len(hs) > 25:
                hs = sorted(hs, key=lambda h: h["parcel"]["amount"])[:30]
                total = sum(h["parcel"]["amount"] for h in hs)
                a = w.address()
                t0 = time.perf_counter()
                w.transact([h["ref"] for h in hs], [model.parcel(a["home"], asset, total, a["lock"], a["salt"])])
                self.ops.append((self.t(), "consolidate", time.perf_counter() - t0))
                for h in hs:
                    self.sealed[h["parcel"]["home"]] = self.sealed.get(h["parcel"]["home"], 0) + 1
                return

    def op_fresh_holder(self):
        src = self.rng.choice(self.holders())
        home = self.rng.choice([cid for cid in (self.R, self.P, self.M, self.H) if cid not in self.down])
        f = Wallet(f"fresh{self.fresh_count}", self.net, home)
        asset = self.assets[self.rng.choice(list(self.assets))]
        if self.funded(src, asset, 1):
            self.fresh_count += 1
            self.pay(src, f, asset, 1, kind="fresh")
            # Keep its balance, not the wallet (its dossier is the whole history of the coin).
            self.fresh[asset] = self.fresh.get(asset, 0) + f.balance(asset)

    def op_save(self, reload: bool):
        name = self.rng.choice([n for n, w in self.wallets.items() if w.home not in self.down])
        w = self.wallets[name]
        d = os.path.join(self.dir, "wallets", name)
        t0 = time.perf_counter()
        wallet_store.save(w, d)
        if reload:
            again = wallet_store.load(d, self.net)
            assert again.holdings == w.holdings and again.pledged == w.pledged
            self.wallets[name] = again
        self.ops.append((self.t(), "reload" if reload else "save", time.perf_counter() - t0))

    def step(self):
        r = self.rng.random()
        if r < 0.33:
            self.op_pay(cross=False)
        elif r < 0.70:
            self.op_pay(cross=True)
        elif r < 0.80:
            self.op_swap()
        elif r < 0.86:
            self.op_consolidate()
        elif r < 0.90:
            self.op_fresh_holder()
        elif r < 0.98:
            self.op_save(reload=False)
        else:
            self.op_save(reload=True)

    # ------------------------------------------------------------ events

    def stop_old(self, idx: list):
        for i in idx:
            p = self.c.procs.get(i)
            if p is None:
                continue
            self.c.kill(i, signal.SIGTERM)
            if p.returncode not in (0, None):
                self.errors.append((self.t(), "exit", f"{self.c.witnesses[i]['name']} exited {p.returncode} on SIGTERM"))

    def rotate(self):
        c, M = self.c, self.M
        kinds = self.rot_cycle[len([e for e in self.events if e[1] == "rotation"]) % len(self.rot_cycle)]
        old = c.indices(M)
        t0 = time.perf_counter()
        new = c.add_members(M, kinds, self.admin)
        c.start_all(new)
        v = self.net.rotate(M, [c.url(i) for i in new], self.token)
        c.write_chain(M, self.net.registry.chain(M))
        for i in new:
            c.witnesses[i]["pending"] = False
        dt = time.perf_counter() - t0
        adopted = sum(store_bytes(c.witnesses[i]["store"]) for i in new)
        self.stop_old(old)
        self.write_urls()
        self.events.append((self.t(), "rotation", {"version": v, "kinds": kinds, "seconds": round(dt, 2),
                                                   "new_store_bytes": adopted}))
        log(f"rotated vega to v{v} {kinds} in {dt:.1f}s")

    def succession(self):
        c, H = self.c, self.H
        old, committee = c.indices(H), c.indices(H, role="standby")
        self.down.add(H)
        t0 = time.perf_counter()
        for i in old:
            c.kill(i, signal.SIGKILL)
        new = c.add_members(H, ["python", "rust", "rust", "python"], self.admin)
        c.start_all(new)
        new_urls = [c.url(i) for i in new]
        nk = c.add_standbys(H, ["rust", "python", "python", "rust"],
                            {k: [*self.admin[k], "--members", *new_urls, "--probe-every", "0.5"] for k in ("rust", "python")})
        c.start_all(nk)
        time.sleep(DEAD_MAN + 1)
        v = None
        for _ in range(30):
            try:
                v = self.net.succeed(H, new_urls, self.token, committee_urls=[c.url(i) for i in nk], dead_man=DEAD_MAN)
                break
            except RuntimeError:
                time.sleep(1)
        if v is None:
            raise AssertionError("the committee never took over")
        c.write_chain(H, self.net.registry.chain(H))
        for i in new:
            c.witnesses[i]["pending"] = False
        self.stop_old(committee)   # fenced
        self.write_urls()
        self.down.discard(H)
        dt = time.perf_counter() - t0
        self.events.append((self.t(), "succession", {"version": v, "seconds": round(dt, 2)}))
        log(f"heir succeeded to v{v} in {dt:.1f}s")

    # ------------------------------------------------------------ measuring

    PROBER = r"""
import json, os, random, sys, time, urllib.request
urls_file, out_file = sys.argv[1], sys.argv[2]
rng = random.Random(7)
with open(out_file, "a", buffering=1) as out:
    while os.path.exists(urls_file):
        try:
            with open(urls_file) as f:
                urls = json.load(f)
        except (OSError, ValueError):
            urls = []
        if urls:
            u = rng.choice(urls)
            body = json.dumps({"sigil": os.urandom(32).hex()}).encode()
            req = urllib.request.Request(u + "/v0/status", data=body, headers={"Content-Type": "application/json"})
            t0 = time.monotonic()
            try:
                with urllib.request.urlopen(req, timeout=5) as r:
                    r.read()
                out.write(f"{t0} {time.monotonic() - t0} {u}\n")
            except OSError:
                pass   # a member being rotated out
        time.sleep(0.05)
"""

    def write_urls(self):
        """The live witnesses' URLs, for the prober process (atomically replaced)."""
        tmp = self.urls_file + ".tmp"
        with open(tmp, "w") as f:
            json.dump([self.c.url(i) for i in list(self.c.procs)], f)
        os.replace(tmp, self.urls_file)

    def start_prober(self):
        """STATUS latency is measured from a separate process: a thread in this one would
        measure the GIL held by the wallets' work, not the witnesses."""
        self.urls_file = os.path.join(self.dir, "probe-urls.json")
        self.probe_out = os.path.join(self.dir, "probe.txt")
        self.write_urls()
        self.prober = subprocess.Popen([sys.executable, "-c", self.PROBER, self.urls_file, self.probe_out],
                                       stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.case.addCleanup(lambda: self.prober.poll() is None and self.prober.kill())

    def stop_prober(self):
        try:
            os.unlink(self.urls_file)
        except FileNotFoundError:
            pass
        try:
            self.prober.wait(10)
        except subprocess.TimeoutExpired:
            self.prober.kill()
        kinds = {self.c.url(i): w["kind"] for i, w in enumerate(self.c.witnesses)}
        with open(self.probe_out) as f:
            for line in f:
                t, dt, u = line.split()
                self.status_lat.append((round(float(t) - self.t0, 3), float(dt), kinds.get(u, "?")))

    def sample(self):
        c = self.c
        procs = {}
        for i, p in list(c.procs.items()):
            st = proc_stats(p.pid)
            if st is None:
                continue
            w = c.witnesses[i]
            st.update(store=store_bytes(w["store"]), log=du(w["log"]), kind=w["kind"], role=w.get("role", "witness"))
            procs[w["name"]] = st
        me = proc_stats(os.getpid())
        wallets = {n: du(os.path.join(self.dir, "wallets", n)) for n in self.wallets}
        held = {n: len(w.holdings) for n, w in self.wallets.items()}
        dossier = {n: len(w.dossier) for n, w in self.wallets.items()}
        disk = du(self.dir)
        s = {"t": self.t(), "procs": procs, "client": me, "wallet_dir_bytes": wallets, "holdings": held,
             "dossier_tx": dossier, "disk": disk, "ops": len(self.ops), "sealed": dict(self.sealed)}
        self.samples.append(s)
        self.check_conservation()
        if disk > MAX_DISK:
            raise AssertionError(f"run directory uses {disk} bytes (> {MAX_DISK})")
        ll = [procs[n] for n in self.long_lived if n in procs]
        log(f"t={s['t']:.0f}s ops={len(self.ops)} disk={disk / MIB:.1f}MiB "
            f"rust rss={max((p['rss'] for p in ll if p['kind'] == 'rust'), default=0) / MIB:.1f}MiB "
            f"py rss={max((p['rss'] for p in ll if p['kind'] == 'python'), default=0) / MIB:.1f}MiB "
            f"client rss={me['rss'] / MIB:.0f}MiB")

    def check_conservation(self):
        for asset, supply in self.supply.items():
            total = sum(w.balance(asset) for w in self.wallets.values()) + self.fresh.get(asset, 0)
            if total != supply:
                self.errors.append((self.t(), "conservation", f"{asset}: {total} != {supply}"))

    # ------------------------------------------------------------ run

    def run(self):
        self.t0 = time.monotonic()
        self.build()
        self.start_prober()
        end = self.t0 + DURATION
        next_sample = time.monotonic()
        next_rotate = self.t0 + ROTATE if ROTATE > 0 else float("inf")
        succession_at = self.t0 + SUCCESSION_AT * DURATION if SUCCESSION_AT >= 0 else float("inf")
        try:
            while time.monotonic() < end:
                now = time.monotonic()
                if now >= next_sample:
                    self.sample()
                    next_sample = now + SAMPLE
                if now >= next_rotate:
                    self.rotate()
                    next_rotate = time.monotonic() + ROTATE
                if now >= succession_at:
                    self.succession()
                    succession_at = float("inf")
                if now - self.series_started >= SERIES:
                    self.new_series()
                try:
                    self.step()
                except Exception as e:  # noqa: BLE001 - every failure is recorded and fails the run
                    self.errors.append((self.t(), type(e).__name__, str(e)[:300], traceback.format_exc()[-1500:]))
                    if len(self.errors) > 20:
                        raise
            self.sample()
        finally:
            self.stop_prober()
        self.restart_check()

    def restart_check(self):
        """Restart one long-lived witness of each kind on its soaked store: same STATUS for the
        sigils the wallets hold there, how long it takes, and its RSS before and after."""
        self.restarts = {}
        for kind, cid in (("rust", self.R), ("python", self.P)):
            i = self.c.indices(cid)[0]
            url = self.c.url(i)
            sigils = sorted({h["sigil"] for w in self.wallets.values() for h in w.holdings.values()
                             if h["parcel"]["home"] == cid})[:200]
            for w in self.wallets.values():   # and spent ones: inputs sealed in cid
                for tx in list(w.dossier.transitions.values())[-100:]:
                    sigils += [s_ for s_, _ in tx["header"]["inputs"]]
            before = {s_: http(url, "/v0/status", {"sigil": s_})[1]["ok"] for s_ in sigils}
            rss_before = proc_stats(self.c.pid(i))["rss"]
            self.c.kill(i, signal.SIGTERM)
            t0 = time.monotonic()
            self.c.start(i)
            self.c.wait_ready(i, timeout=120)
            ready = time.monotonic() - t0
            time.sleep(1)
            rss_after = proc_stats(self.c.pid(i))["rss"]
            after = {s_: http(url, "/v0/status", {"sigil": s_})[1]["ok"] for s_ in sigils}
            self.restarts[kind] = {"ready_s": round(ready, 2), "rss_before": rss_before, "rss_after_reload": rss_after,
                                   "store": store_bytes(self.c.witnesses[i]["store"]), "sigils_checked": len(before),
                                   "identical": before == after}
            log(f"restart {kind}: {self.restarts[kind]}")

    # ------------------------------------------------------------ results

    def summary(self) -> dict:
        warm = [s for s in self.samples if s["t"] >= 0.2 * DURATION] or self.samples
        first, last = warm[0], self.samples[-1]
        per_proc = {}
        for name in self.long_lived:
            seq = [s["procs"][name] for s in warm if name in s["procs"]]
            if len(seq) < 2:
                continue
            per_proc[name] = {
                "kind": seq[0]["kind"],
                "rss_start": seq[0]["rss"], "rss_end": seq[-1]["rss"], "rss_max": max(p["rss"] for p in seq),
                "fds_start": seq[0]["fds"], "fds_max": max(p["fds"] for p in seq),
                "threads_start": seq[0]["threads"], "threads_max": max(p["threads"] for p in seq),
                "store_start": seq[0]["store"], "store_end": seq[-1]["store"],
                "log_start": seq[0]["log"], "log_end": seq[-1]["log"],
            }
        third = max(1, len(self.ops) // 3)
        for name, p in per_proc.items():
            cid = self.c.witnesses[self.long_lived[name]]["cid"]
            n = last["sealed"].get(cid, 0) - first["sealed"].get(cid, 0)
            p["store_bytes_per_sealed_input"] = (p["store_end"] - p["store_start"]) / n if n else None
            p["rss_bytes_per_sealed_input"] = (p["rss_end"] - p["rss_start"]) / n if n else None

        def window(xs, lo, hi):
            return [x for t, x in xs if lo <= t < hi]

        T = self.samples[-1]["t"]
        stat = [(t, dt) for t, dt, _ in self.status_lat]
        stat_w = [percentiles(window(stat, a * T / 3, (a + 1) * T / 3)) for a in range(3)]
        stat_kind = {k: percentiles([dt for _, dt, kk in self.status_lat if kk == k]) for k in ("rust", "python")}
        seal = [(h["t"], h["seal"]) for h in self.hops if h["kind"] in ("pay", "cross")]
        seal_w = [percentiles(window(seal, a * T / 3, (a + 1) * T / 3)) for a in range(3)]
        by_kind = {}
        for _, k, dt in self.ops:
            by_kind.setdefault(k, []).append(dt)
        hops = [h for h in self.hops if h["ntx"] > 0]
        fresh = [h for h in hops if h["kind"] == "fresh"]
        return {
            "config": {"duration": DURATION, "sample": SAMPLE, "rotate": ROTATE, "series": SERIES, "seed": SEED,
                       "succession_at": SUCCESSION_AT},
            "ops_total": len(self.ops), "ops_per_s": len(self.ops) / max(T, 1e-9),
            "ops": {k: percentiles(v) for k, v in by_kind.items()},
            "status_latency_windows": stat_w, "status_latency_by_kind": stat_kind, "seal_latency_windows": seal_w,
            "sealed_inputs": dict(self.sealed),
            "long_lived": per_proc,
            "client_rss": {"start": first["client"]["rss"], "end": last["client"]["rss"]},
            "disk_end": last["disk"], "wallet_dir_bytes_end": last["wallet_dir_bytes"],
            "holdings_end": last["holdings"], "dossier_tx_end": last["dossier_tx"],
            "hop_ntx_max": max((h["ntx"] for h in hops), default=0),
            "hop_bytes_max": max((h["bytes"] for h in hops), default=0),
            "hop_bytes_per_tx": percentiles([h["bytes"] / h["ntx"] for h in hops]),
            "hop_verify_per_new_tx": percentiles([h["verify"] / h["new"] for h in hops if h["new"] > 0]),
            "fresh_verify_per_tx": percentiles([h["verify"] / h["ntx"] for h in fresh]),
            "pack_per_tx": percentiles([h["pack"] / h["ntx"] for h in hops]),
            "events": self.events, "errors": self.errors, "third": third,
            "restarts": getattr(self, "restarts", {}),
        }


@requires_rust
class SoakTest(unittest.TestCase):
    def test_soak(self):
        soak = Soak(self)
        log(f"soak for {DURATION:.0f}s in {soak.dir}")
        try:
            soak.run()
        finally:
            summary = soak.summary() if soak.samples else {"errors": soak.errors}
            out = ENV("SIGIL_SOAK_OUT")
            if out:
                with open(out, "w") as f:
                    json.dump({"summary": summary, "samples": soak.samples, "hops": soak.hops, "ops": soak.ops,
                               "status_latency": soak.status_lat}, f, default=str)
        s = summary
        log(json.dumps({k: s[k] for k in ("ops_total", "ops_per_s", "status_latency_windows", "seal_latency_windows",
                                           "hop_ntx_max", "hop_bytes_max", "disk_end")}, default=str))
        self.assertEqual(s["errors"], [], "operations failed or value was not conserved")
        for kind, r in s["restarts"].items():
            self.assertTrue(r["identical"], f"{kind}: STATUS changed across a restart on the soaked store: {r}")
            self.assertLess(r["ready_s"], 60, r)
        self.assertGreater(s["ops_total"], DURATION / 10, "the workload hardly ran")
        if ROTATE > 0 and DURATION >= ROTATE * 1.5:
            self.assertTrue(any(e[1] == "rotation" for e in s["events"]))
        if 0 <= SUCCESSION_AT < 1:
            self.assertTrue(any(e[1] == "succession" for e in s["events"]))
        for name, p in s["long_lived"].items():
            with self.subTest(process=name):
                growth = max(0, p["store_end"] - p["store_start"])
                self.assertLessEqual(p["rss_end"] - p["rss_start"], 64 * MIB + 3 * growth,
                                     f"{name}: RSS grew more than its data explains: {p}")
                self.assertLessEqual(p["fds_max"] - p["fds_start"], 16, f"{name}: open fds grew: {p}")
                cap = 600 if p["kind"] == "rust" else 80
                self.assertLessEqual(p["threads_max"], cap, f"{name}: threads: {p}")
                self.assertLessEqual(p["log_end"] - p["log_start"], 64 * 1024, f"{name}: log grows with traffic: {p}")
        # Store growth per sealed input, first vs second half, per long-lived constellation.
        half = [x for x in soak.samples if x["t"] >= DURATION / 2] or soak.samples
        mid, w0, end = half[0], soak.samples[0], soak.samples[-1]
        for cid in (soak.R, soak.P):
            names = [n for n, i in soak.long_lived.items() if soak.c.witnesses[i]["cid"] == cid]
            ops1 = mid["sealed"].get(cid, 0) - w0["sealed"].get(cid, 0)
            ops2 = end["sealed"].get(cid, 0) - mid["sealed"].get(cid, 0)
            for n in names:
                if n not in w0["procs"] or n not in end["procs"] or ops1 < 20 or ops2 < 20:
                    continue
                b1 = (mid["procs"][n]["store"] - w0["procs"][n]["store"]) / ops1
                b2 = (end["procs"][n]["store"] - mid["procs"][n]["store"]) / ops2
                with self.subTest(store=n):
                    self.assertLess(b2, 256 * 1024, f"{n}: {b2:.0f} bytes per op")
                    # A redb file grows by doubling, so its size per op over a window is a step
                    # function; the super-linear check is for SQLite, which grows smoothly.
                    if soak.c.witnesses[soak.long_lived[n]]["kind"] == "python":
                        self.assertLessEqual(b2, 2 * max(b1, 0) + 4096, f"{n}: store growth per op rose {b1:.0f} -> {b2:.0f}")
        # redb against SQLite for the same kind of data: at most ~2x, plus one doubling step.
        per_op = {p["kind"]: p["store_bytes_per_sealed_input"] for p in s["long_lived"].values()
                  if p.get("store_bytes_per_sealed_input")}
        if "rust" in per_op and "python" in per_op:
            self.assertLessEqual(per_op["rust"], 4.5 * per_op["python"] + 4096, per_op)
        # Witness-side slowdown.
        st, se = s["status_latency_windows"], s["seal_latency_windows"]
        if st[0]["n"] >= 20 and st[2]["n"] >= 20:
            self.assertLessEqual(st[2]["p50"], 3 * st[0]["p50"] + 0.02, f"STATUS slowed down: {st}")
        if se[0]["n"] >= 20 and se[2]["n"] >= 20:
            self.assertLessEqual(se[2]["p50"], 3 * se[0]["p50"] + 0.2, f"sealing slowed down: {se}")
        # Dossiers: bounded bytes per transition; fresh verification cost per transition bounded.
        self.assertLess(s["hop_bytes_per_tx"]["p99"] or 0, 16 * 1024, s["hop_bytes_per_tx"])
        if s["fresh_verify_per_tx"]["n"]:
            self.assertLess(s["fresh_verify_per_tx"]["p50"], 0.05, s["fresh_verify_per_tx"])


if __name__ == "__main__":
    unittest.main()
