#!/usr/bin/env python3
"""Python-side benchmarks. Each subcommand prints one JSON object.

    python3 bench/bench_python.py inproc  --n 3000 [--store]       # reference witness, votes/s
    python3 bench/bench_python.py seal    --sizes 4,7,10,31,100     # reference verify_seal
    python3 bench/bench_python.py dossier --lengths 1,10,100,1000   # holder-side verification vs history
    python3 bench/bench_python.py latency --kind rust|python --n 200   # end-to-end payment over HTTP
"""

import argparse
import json
import os
import shutil
import signal
import statistics
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import Cluster, compat_wallet_class  # noqa: E402

from sigil import Network, model  # noqa: E402
from sigil.charter import Registry, charter_body, constellation_id, quorum  # noqa: E402
from sigil.crypto import KeyPair  # noqa: E402
from sigil.locks import empty_unlock, sig, sign_unlock  # noqa: E402
from sigil.proofs import verify_seal  # noqa: E402
from sigil.server import RemoteNetwork  # noqa: E402
from sigil.store import WitnessStore  # noqa: E402
from sigil.validate import TrustPolicy, Verifier  # noqa: E402
from sigil.witness import Witness  # noqa: E402


def pct(xs, p):
    xs = sorted(xs)
    return xs[round((len(xs) - 1) * p)] if xs else 0.0


def constellation(n, tag):
    keys = [KeyPair.from_seed(f"{tag}-{i}".encode()) for i in range(n)]
    body = charter_body(tag, 0, [k.pk for k in keys], None)
    cid = constellation_id(body)
    reg = Registry()
    reg.add_chain(cid, [{"body": body, "sigs": {}}])
    return keys, cid, reg


def requests(cid, n, tag):
    owner = KeyPair.from_seed(b"bench-owner")
    exp = int(time.time()) + 86400
    out = []
    for i in range(n):
        lock = sig(owner.pk)
        salt = f"{tag}-{i:08}"
        s = model.sigil_of({"home": cid, "lock": lock, "salt": salt})
        h = {"inputs": [[s, 0]], "body": "b" * 64}
        tid = model.transition_id(h)
        u = empty_unlock(exp)
        u["sigs"][owner.pk] = sign_unlock(owner, s, tid, exp)
        out.append(json.dumps({"sigil": s, "header": h, "home": cid, "lock": lock, "salt": salt, "unlock": u}).encode())
    return out


def bench_inproc(args):
    keys, cid, reg = constellation(4, "pybench")
    tmp = tempfile.mkdtemp(prefix="sigil-pybench-")
    store = WitnessStore(os.path.join(tmp, "w.db")) if args.store else None
    w = Witness(keys[0], reg, lambda: int(time.time()), store=store)
    w.join(cid, 0)
    reqs = requests(cid, args.n, "inproc")
    t0 = time.perf_counter()
    for r in reqs:
        v = w.spend(json.loads(r))
        json.dumps({"ok": v}).encode()   # the reply, as the server would encode it
    dt = time.perf_counter() - t0
    shutil.rmtree(tmp, ignore_errors=True)
    return {"bench": "python_inproc", "store": "sqlite" if args.store else "memory", "n": args.n,
            "seconds": dt, "votes_per_s": args.n / dt, "us_per_vote": dt * 1e6 / args.n}


def bench_seal(args):
    rows = []
    for n in (int(x) for x in args.sizes.split(",")):
        keys, cid, reg = constellation(n, f"pyseal-{n}")
        q = quorum(n)
        votes = []
        for k in keys[:q]:
            v = {"constellation": cid, "version": 0, "witness": k.pk, "sigil": "s" * 64, "gen": 0, "tid": "e" * 64,
                 "time": 1700000000}
            v["sig"] = k.sign("vote", model.vote_payload(v))
            votes.append(v)
        seal = model.seal_from_votes(votes)
        assert verify_seal(seal, reg)
        it = max(10, 2000 // n)
        t0 = time.perf_counter()
        for _ in range(it):
            verify_seal(seal, reg)
        rows.append({"witnesses": n, "quorum": q, "seal_us": (time.perf_counter() - t0) * 1e6 / it})
    return {"bench": "python_seal", "rows": rows}


def bench_dossier(args):
    """A coin passed back and forth L times: verify the received parcel from scratch."""
    W = compat_wallet_class()
    lengths = sorted(int(x) for x in args.lengths.split(","))
    net = Network()
    X = net.create_constellation("orion", n=4)
    alice, bob = W("alice", net, X), W("bob", net, X)
    usd = alice.issue("USD", 100)
    wallets, hops, rows = (alice, bob), 0, []
    t_build = time.perf_counter()
    for L in lengths:
        while hops < L:
            src, dst = wallets[hops % 2], wallets[(hops + 1) % 2]
            tid = src.pay(dst, usd, 100)
            net.clock.advance(1)
            hops += 1
        holder = wallets[hops % 2]
        d = holder.dossier.ancestry([tid])
        ref = model.ref(tid, 0)
        size = len(d.to_json())
        reps = max(1, 50 // L)
        t0 = time.perf_counter()
        for _ in range(reps):
            Verifier(TrustPolicy(net.registry)).verify_parcel(d, ref)   # cold: nothing cached
        cold = (time.perf_counter() - t0) / reps
        rows.append({"history": L, "transitions": len(d), "seals": len(d.seals), "dossier_bytes": size,
                     "verify_ms": cold * 1e3, "per_transition_us": cold * 1e6 / len(d)})
    # Warm: a holder that already verified the history checks one more hop.
    src, dst = wallets[hops % 2], wallets[(hops + 1) % 2]
    v = Verifier(TrustPolicy(net.registry))
    v.verify_parcel(src.dossier.ancestry([tid]), model.ref(tid, 0))
    tid2 = src.pay(dst, usd, 100)
    t0 = time.perf_counter()
    v.verify_parcel(dst.dossier.ancestry([tid2]), model.ref(tid2, 0))
    warm = time.perf_counter() - t0
    return {"bench": "python_dossier", "rows": rows, "warm_one_hop_ms": warm * 1e3,
            "build_seconds": time.perf_counter() - t_build}


def bench_latency(args):
    W = compat_wallet_class()
    tmp = tempfile.mkdtemp(prefix="sigil-latency-")
    c = Cluster(tmp)
    try:
        X = c.create("orion", [args.kind] * args.witnesses)
        c.start_all()
        net = RemoteNetwork(c.directory(), timeout=10)
        alice, bob = W("alice", net, X), W("bob", net, X)
        usd = alice.issue("USD", 10 ** 9)
        for _ in range(5):                      # warm up
            alice.pay(bob, usd, 1)
        lat, seal_lat = [], []
        for i in range(args.n):
            t0 = time.perf_counter()
            alice.pay(bob, usd, 1)
            lat.append((time.perf_counter() - t0) * 1e3)
        # Sealing alone (the witness round trips), without the recipient's verification.
        for i in range(args.n):
            addr = bob.address()
            refs, outputs = alice.payment_outputs(usd, 1, addr)
            header, body, _ = alice.prepare(refs, outputs)
            unlocks = alice.authorise(header, body)
            t0 = time.perf_counter()
            alice.seal(header, body, unlocks)
            seal_lat.append((time.perf_counter() - t0) * 1e3)
            alice.finalise(header, body, unlocks)
        return {"bench": "payment_latency", "witnesses": args.kind, "n_witnesses": args.witnesses, "n": args.n,
                "pay_p50_ms": pct(lat, .5), "pay_p90_ms": pct(lat, .9), "pay_p99_ms": pct(lat, .99),
                "pay_mean_ms": statistics.mean(lat),
                "seal_p50_ms": pct(seal_lat, .5), "seal_p99_ms": pct(seal_lat, .99)}
    finally:
        c.stop_all(signal.SIGTERM)
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("inproc")
    p.add_argument("--n", type=int, default=3000)
    p.add_argument("--store", action="store_true")
    p = sub.add_parser("seal")
    p.add_argument("--sizes", default="4,7,10,31,100")
    p = sub.add_parser("dossier")
    p.add_argument("--lengths", default="1,10,100,1000")
    p = sub.add_parser("latency")
    p.add_argument("--kind", choices=["rust", "python"], default="rust")
    p.add_argument("--n", type=int, default=200)
    p.add_argument("--witnesses", type=int, default=4)
    args = ap.parse_args()
    fn = {"inproc": bench_inproc, "seal": bench_seal, "dossier": bench_dossier, "latency": bench_latency}[args.cmd]
    print(json.dumps(fn(args)))


if __name__ == "__main__":
    main()
