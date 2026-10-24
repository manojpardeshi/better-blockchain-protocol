"""Measure how Sigil dossiers grow (Phase 3, #10).

Builds realistic histories with the reference ``sigil.Wallet`` (payments,
merges, atomic swaps) on the in-process network and reports, for the
dossier a payee receives:

* size: transitions, seals, votes, charters, canonical-JSON bytes, zlib
  bytes, and an estimate of a compact binary encoding (hex counted as raw
  bytes, small per-field overhead);
* verification time for a *cold* holder (empty cache: what a first-time
  recipient pays) and, in the economy scenario, for the *actual* payee
  (warm cache: only history new to it).

Scenarios
---------
chain     one parcel paid hop after hop (no merges): linear in hops.
fanin     a merchant collects K payments whose coins each travelled H hops,
          then consolidates; repeated L levels: K^L * H growth.
economy   M wallets, two assets, random payments with coin selection (merges)
          and occasional atomic swaps: ancestry coverage of the whole asset
          history over time.
committee per-hop bytes as a function of constellation size n.

Usage::

    python3 -m research.measure_dossiers                # all scenarios, default sizes
    python3 -m research.measure_dossiers --quick        # small, for a smoke test
    python3 -m research.measure_dossiers --json out.json
"""

import argparse
import json
import random
import statistics
import time
import zlib

try:
    from research import _compat  # noqa: F401  (puts the repo root on sys.path)
except ImportError:  # run as a script from inside research/
    import _compat  # noqa: F401

from sigil import Network, TrustPolicy, Verifier, Wallet, model
from sigil.swap import atomic_swap
from sigil.validate import Dossier


# ----------------------------------------------------------------- metrics

def _is_hex(s: str) -> bool:
    return len(s) >= 2 and len(s) % 2 == 0 and all(c in "0123456789abcdef" for c in s)


def binary_estimate(x) -> int:
    """Rough size of a compact binary encoding of a JSON-native value.

    Hex strings count as raw bytes; every map entry costs one tag byte for
    its key (a schema'd encoding would not repeat key names); integers
    cost 8 bytes, other strings their length plus one.
    """
    if isinstance(x, dict):
        return 1 + sum(1 + binary_estimate(v) for v in x.values())
    if isinstance(x, list):
        return 1 + sum(binary_estimate(v) for v in x)
    if isinstance(x, str):
        return len(x) // 2 if _is_hex(x) else len(x) + 1
    if isinstance(x, bool) or x is None:
        return 1
    if isinstance(x, int):
        return 8
    return len(str(x))


def dossier_stats(d: Dossier) -> dict:
    raw = d.to_json().encode()
    obj = {"transitions": d.transitions, "seals": d.seals, "charters": d.charters}
    # Seal map keys are "sigil:tid", which binary_estimate cannot see; the
    # values already carry sigil and tid, so a binary form need not repeat them.
    return {
        "transitions": len(d.transitions),
        "seals": len(d.seals),
        "votes": sum(len(s["votes"]) for s in d.seals.values()),
        "charters": sum(len(c) for c in d.charters.values()),
        "json_bytes": len(raw),
        "zlib_bytes": len(zlib.compress(raw, 9)),
        "binary_est_bytes": binary_estimate(obj),
    }


def verify_cold(net: Network, d: Dossier, r: dict, reps: int = 1) -> float:
    """Seconds for a holder with an empty cache to verify parcel ``r`` (best of reps)."""
    best = float("inf")
    for _ in range(reps):
        v = Verifier(TrustPolicy(net.registry))
        t0 = time.perf_counter()
        v.verify_parcel(d, r)
        best = min(best, time.perf_counter() - t0)
    return best


def pay_measured(payer: Wallet, payee: Wallet, asset: str, amount: int, home=None) -> tuple:
    """Like ``Wallet.pay``, but returns (tid, dossier, new_transitions, warm_seconds)."""
    addr = payee.address(home)
    refs, outputs = payer.payment_outputs(asset, amount, addr)
    tid = payer.transact(refs, outputs)
    d = payer.dossier.ancestry([tid])
    new = len(set(d.transitions) - payee.verifier._ok)  # history new to this payee
    t0 = time.perf_counter()
    payee.receive(d, [model.ref(tid, 0)])
    return tid, d, new, time.perf_counter() - t0


# --------------------------------------------------------------- scenarios

def scenario_chain(hops: int, n: int = 4, samples=None, reps: int = 3) -> list:
    """One parcel, paid on in full each hop, alternating between two homes."""
    net = Network()
    homes = [net.create_constellation("orion", n), net.create_constellation("lyra", n)]
    issuer = Wallet("issuer", net, homes[0])
    asset = issuer.issue("USD", 1_000)
    samples = set(samples or [h for h in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512) if h <= hops] + [hops])
    rows, holder = [], issuer
    for h in range(1, hops + 1):
        nxt = Wallet(f"w{h}", net, homes[h % 2])
        tid = holder.pay(nxt, asset, 1_000)
        holder = nxt
        if h in samples:
            d = holder.dossier.ancestry([tid])
            row = {"hops": h, **dossier_stats(d), "verify_cold_ms": 1e3 * verify_cold(net, d, model.ref(tid, 0), reps)}
            rows.append(row)
    return rows


def _chain_of(net, issuer, asset, homes, hops, amount, tag):
    """Pay ``amount`` from issuer down a fresh chain of ``hops`` wallets; return the last wallet."""
    holder = issuer
    for h in range(hops):
        nxt = Wallet(f"{tag}-{h}", net, homes[(h + 1) % len(homes)])
        holder.pay(nxt, asset, amount)
        holder = nxt
    return holder


def scenario_fanin(k: int, hops: int, levels: int, n: int = 4, reps: int = 1) -> list:
    """K-ary consolidation tree over coins that each travelled ``hops`` hops.

    Level 1: K customers (each holding a coin with a ``hops``-hop history)
    pay one merchant, who consolidates and pays a supplier. Level l: K
    level-(l-1) suppliers pay one level-l supplier. The final parcel's
    ancestry contains K^levels chains.
    """
    net = Network()
    homes = [net.create_constellation("orion", n), net.create_constellation("lyra", n)]
    issuer = Wallet("issuer", net, homes[0])
    leaves = k ** levels
    asset = issuer.issue("USD", 10 * leaves)
    holders = [_chain_of(net, issuer, asset, homes, hops, 10, f"leaf{i}") for i in range(leaves)]
    rows = []
    for level in range(1, levels + 1):
        nxt = []
        for g in range(0, len(holders), k):
            merchant = Wallet(f"m{level}-{g}", net, homes[level % 2])
            for c in holders[g:g + k]:
                c.pay(merchant, asset, c.balance(asset))
            supplier = Wallet(f"s{level}-{g}", net, homes[(level + 1) % 2])
            tid, d, _, _ = pay_measured(merchant, supplier, asset, merchant.balance(asset))
            nxt.append((supplier, tid, d))
        supplier, tid, d = nxt[0]
        rows.append({"k": k, "hops": hops, "level": level, "leaf_chains": k ** level,
                     **dossier_stats(d), "verify_cold_ms": 1e3 * verify_cold(net, d, model.ref(tid, 0), reps)})
        holders = [s for s, _, _ in nxt]
    return rows


def scenario_economy(wallets: int, payments: int, n: int = 4, swap_every: int = 15,
                     sample_every: int = 20, seed: int = 7) -> dict:
    """Random payments (with coin-selection merges) and periodic atomic swaps."""
    rng = random.Random(seed)
    net = Network()
    homes = [net.create_constellation(name, n) for name in ("orion", "lyra", "vega")]
    ws = [Wallet(f"w{i}", net, homes[i % len(homes)]) for i in range(wallets)]
    usd = ws[0].issue("USD", 1_000_000)
    gold = ws[1].issue("GOLD", 1_000_000, homes[1])
    total = {usd: 1, gold: 1}  # transitions in each asset's history (genesis counted)
    tx_assets: dict[str, set] = {usd: {usd}, gold: {gold}}

    def record(tid, assets):
        tx_assets[tid] = set(assets)
        for a in assets:
            total[a] += 1

    # Seed every wallet with both assets.
    for w in ws[2:]:
        record(ws[0].pay(w, usd, 20_000), [usd])
        record(ws[1].pay(w, gold, 20_000), [gold])
    rows = []
    for i in range(1, payments + 1):
        if swap_every and i % swap_every == 1:  # never collides with the sampling steps used here
            a, b = rng.sample(ws, 2)
            if a.balance(usd) >= 10 and b.balance(gold) >= 10:
                tid = atomic_swap(a, usd, rng.randint(1, a.balance(usd) // 4 or 1),
                                  b, gold, rng.randint(1, b.balance(gold) // 4 or 1))
                record(tid, [usd, gold])
            continue
        asset = rng.choice([usd, gold])
        rich = [w for w in ws if w.balance(asset) >= 2]
        payer = rng.choice(rich)
        payee = rng.choice([w for w in ws if w is not payer])
        amount = rng.randint(1, max(1, payer.balance(asset) // 2))
        tid, d, new, warm = pay_measured(payer, payee, asset, amount, rng.choice(homes))
        record(tid, [asset])
        if i % sample_every == 0 or i == payments:
            st = dossier_stats(d)
            n_all = len(tx_assets)  # every transition so far, both assets, both geneses
            rows.append({"payment": i, "asset": "USD" if asset == usd else "GOLD", **st,
                         "history_total": n_all, "asset_history": total[asset],
                         "coverage": round(st["transitions"] / n_all, 3),
                         "new_to_payee": new, "verify_warm_ms": 1e3 * warm,
                         "verify_cold_ms": 1e3 * verify_cold(net, d, model.ref(tid, 0))})
    return {"rows": rows, "wallets": wallets, "payments": payments, "swap_every": swap_every}


def scenario_committee(sizes=(4, 7, 10, 16, 31), hops: int = 32) -> list:
    rows = []
    for n in sizes:
        r = scenario_chain(hops, n, samples=[hops], reps=1)[-1]
        rows.append({"n": n, "quorum": n - (n - 1) // 3, **r,
                     "bytes_per_hop_json": round(r["json_bytes"] / hops),
                     "bytes_per_hop_bin": round(r["binary_est_bytes"] / hops)})
    return rows


# ------------------------------------------------------------------ report

def table(rows: list, cols: list) -> str:
    out = ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
    for r in rows:
        cells = []
        for c in cols:
            v = r.get(c, "")
            cells.append(f"{v:,.1f}" if isinstance(v, float) else (f"{v:,}" if isinstance(v, int) else str(v)))
        out.append("| " + " | ".join(cells) + " |")
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--quick", action="store_true", help="small sizes, for a smoke test")
    ap.add_argument("--json", help="write raw results to this file")
    ap.add_argument("--economy-payments", type=int, default=900)
    ap.add_argument("--only", choices=["chain", "fanin", "economy", "committee"], action="append")
    args = ap.parse_args(argv)
    q = args.quick
    want = set(args.only or ["chain", "fanin", "economy", "committee"])
    res = {}
    t0 = time.time()
    if "chain" in want:
        res["chain"] = scenario_chain(16 if q else 512)
        print("\n## chain (n=4, one parcel, no merges)\n")
        print(table(res["chain"], ["hops", "transitions", "seals", "votes", "json_bytes", "zlib_bytes",
                                   "binary_est_bytes", "verify_cold_ms"]))
    if "fanin" in want:
        res["fanin"] = scenario_fanin(2 if q else 4, 2 if q else 8, 2 if q else 3)
        print("\n## fan-in (K-ary consolidation of H-hop coins)\n")
        print(table(res["fanin"], ["k", "hops", "level", "leaf_chains", "transitions", "seals", "votes",
                                   "json_bytes", "binary_est_bytes", "verify_cold_ms"]))
    if "economy" in want:
        res["economy"] = scenario_economy(8 if q else 24, 60 if q else args.economy_payments,
                                          sample_every=10 if q else max(10, args.economy_payments // 20))
        rows = res["economy"]["rows"]
        print(f"\n## economy ({res['economy']['wallets']} wallets, 2 assets, 3 homes, swap every "
              f"{res['economy']['swap_every']}th step)\n")
        print(table(rows, ["payment", "asset", "transitions", "history_total", "coverage", "seals",
                           "json_bytes", "binary_est_bytes", "new_to_payee", "verify_warm_ms", "verify_cold_ms"]))
        late = [r for r in rows if r["payment"] > res["economy"]["payments"] // 2]
        if late:
            res["economy"]["late_median_coverage"] = statistics.median(r["coverage"] for r in late)
            print(f"\nmedian ancestry coverage in second half: {res['economy']['late_median_coverage']:.0%}")
    if "committee" in want:
        res["committee"] = scenario_committee((4, 7) if q else (4, 7, 10, 16, 31), 8 if q else 32)
        print("\n## constellation size (chain of 32 hops)\n")
        print(table(res["committee"], ["n", "quorum", "hops", "votes", "json_bytes", "bytes_per_hop_json",
                                       "bytes_per_hop_bin", "verify_cold_ms"]))
    res["elapsed_s"] = round(time.time() - t0, 1)
    if args.json:
        with open(args.json, "w") as f:
            json.dump(res, f, indent=1)
    print(f"\n(done in {res['elapsed_s']} s)")
    return res


if __name__ == "__main__":
    main()
