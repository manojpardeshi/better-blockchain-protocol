#!/usr/bin/env python3
"""Run every benchmark and write bench/results.json (summarised in docs/BENCHMARKS.md).

    cargo build --release --manifest-path rust/Cargo.toml
    python3 bench/run_all.py [--quick] [--out bench/results.json]

Durable benchmarks are dominated by the disk's flush latency, which on a shared VM moves
around between runs, so they are repeated (``--reps``) with Rust and Python interleaved, a
raw fsync probe is recorded next to them, and the median and the range are reported.
"""

import argparse
import json
import os
import platform
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import RUST_BIN, ROOT, Cluster  # noqa: E402

BENCH_BIN = os.path.join(os.path.dirname(RUST_BIN), "sigil-bench")
PY = [sys.executable, os.path.join(ROOT, "bench", "bench_python.py")]


def sh(cmd, **kw) -> dict:
    out = subprocess.run(cmd, capture_output=True, text=True, check=True, cwd=ROOT, **kw)
    return json.loads(out.stdout.strip().splitlines()[-1])


def rust(*args, pin=None) -> dict:
    return sh([*(["taskset", "-c", pin] if pin else []), BENCH_BIN, *args])


def python(*args) -> dict:
    return sh([*PY, *args])


def summary(runs: list, key: str) -> dict:
    xs = [r[key] for r in runs]
    return {"median": statistics.median(xs), "min": min(xs), "max": max(xs), "runs": runs}


def machine() -> dict:
    def cmd(*c):
        try:
            return subprocess.run(c, capture_output=True, text=True).stdout.strip()
        except OSError:
            return None
    cpu = next((line.split(":", 1)[1].strip() for line in open("/proc/cpuinfo") if line.startswith("model name")), None)
    import cryptography
    import ssl
    return {"cpu": cpu, "cores": os.cpu_count(), "kernel": platform.release(), "python": platform.python_version(),
            "cryptography": cryptography.__version__, "openssl": ssl.OPENSSL_VERSION, "rustc": cmd("rustc", "--version"),
            "filesystem": cmd("df", "-T", "/tmp"), "virtualisation": cmd("systemd-detect-virt") or "unknown",
            "date": time.strftime("%Y-%m-%d %H:%M:%S %Z")}


def http_server(kind: str, extra: list, pin: str):
    tmp = tempfile.mkdtemp(prefix="sigil-httpbench-")
    c = Cluster(tmp, wrap=["taskset", "-c", pin])
    c.create("bench", [kind], extra_args={kind: extra})
    c.start_all()
    return c, tmp


def stop(c, tmp):
    c.stop_all(signal.SIGTERM)
    shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--out", default=os.path.join(ROOT, "bench", "results.json"))
    a = ap.parse_args()
    reps = 1 if a.quick else a.reps
    q = (lambda full, quick: quick if a.quick else full)
    res = {"machine": machine(), "fsync": [rust("fsync", "--iters", "500")]}

    print("in-process votes/s ...", flush=True)
    inproc = {k: [] for k in ("rust_memory_1t", "python_memory", "rust_redb_1t", "python_sqlite", "rust_redb_32t", "rust_memory_4t")}
    for _ in range(reps):
        inproc["rust_memory_1t"].append(rust("inproc", "--n", q("20000", "3000"), "--threads", "1", "--store", "memory", pin="0"))
        inproc["python_memory"].append(python("inproc", "--n", q("3000", "500")))
        inproc["rust_redb_1t"].append(rust("inproc", "--n", q("1500", "300"), "--threads", "1", "--store", "redb"))
        inproc["python_sqlite"].append(python("inproc", "--n", q("1500", "300"), "--store"))
        inproc["rust_redb_32t"].append(rust("inproc", "--n", q("20000", "3000"), "--threads", "32", "--store", "redb"))
        inproc["rust_memory_4t"].append(rust("inproc", "--n", q("40000", "4000"), "--threads", "4", "--store", "memory"))
    res["inproc"] = {k: summary(v, "votes_per_s") for k, v in inproc.items()}

    print("seal verification ...", flush=True)
    res["seal"] = {"rust": rust("seal", "--iters", q("2000", "200")), "python": python("seal")}

    print("HTTP votes/s, witness pinned to one core ...", flush=True)
    http = {}
    configs = [
        ("rust_durable", "rust", ["--threads", "1"], [("c1", "1", False), ("c16", "16", False), ("c64", "64", False), ("c16_newconn", "16", True)]),
        ("python_durable", "python", [], [("c1", "1", False), ("c16", "16", False)]),
        ("rust_memory", "rust", ["--threads", "1", "--unsafe-memory-store"], [("c16", "16", False)]),
    ]
    for _ in range(reps):
        for name, kind, extra, loads in configs:
            c, tmp = http_server(kind, extra, "0")
            try:
                for lname, conc, newc in loads:
                    n = q("20000", "2000") if kind == "rust" else q("3000", "500")
                    if lname == "c1":
                        n = q("1000", "200")
                    args = ["http", "--url", c.url(0), "--n", n, "--concurrency", conc, "--gen-threads", "3"]
                    if newc:
                        args.append("--new-conn")
                    http.setdefault(f"{name}_{lname}", []).append(rust(*args, pin="1-3"))
            finally:
                stop(c, tmp)
    res["http"] = {k: summary(v, "votes_per_s") for k, v in http.items()}

    print("payment latency (Python wallet, 4 witnesses over HTTP) ...", flush=True)
    lat = {"rust": [], "python": []}
    for _ in range(reps):
        for kind in ("rust", "python"):
            lat[kind].append(python("latency", "--kind", kind, "--n", q("200", "30")))
    res["latency"] = {k: summary(v, "pay_p50_ms") for k, v in lat.items()}

    print("holder-side dossier verification ...", flush=True)
    res["dossier"] = python("dossier", "--lengths", q("1,10,100,1000", "1,10,100"))
    res["fsync"].append(rust("fsync", "--iters", "500"))

    with open(a.out, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
    print(json.dumps({"inproc": {k: round(v["median"]) for k, v in res["inproc"].items()},
                      "http": {k: round(v["median"]) for k, v in res["http"].items()},
                      "latency_p50_ms": {k: round(v["median"], 2) for k, v in res["latency"].items()}}, indent=1))
    print("wrote", a.out)


if __name__ == "__main__":
    main()
