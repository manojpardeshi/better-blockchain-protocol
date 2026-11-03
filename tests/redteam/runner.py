"""Run the red-team harness from the command line and print JSON statistics.

    python -m tests.redteam.runner

Env-var knobs (all optional):

    SIGIL_REDTEAM_SEEDS   schedule-explorer seeds           (default 60)
    SIGIL_REDTEAM_STEPS   steps per seed                    (default 150)
    SIGIL_REDTEAM_CONSERVE_SEEDS  payment-fuzzer seeds      (default 20)
    SIGIL_REDTEAM_CONSERVE_STEPS  payment-fuzzer steps      (default 60)
    SIGIL_REDTEAM_TIME    wall-clock budget in seconds; when set, the explorer
                          keeps running fresh seed batches until the budget is
                          spent (overrides SEEDS)
    SIGIL_REDTEAM_NS      constellation sizes to sweep, comma list (default 4,7,10)
    SIGIL_REDTEAM_BEYOND  if "1", also run b = f+1 (expected to find S1)
"""

import json
import os
import time

from . import conserve, model, resources


def _int(name, default):
    return int(os.environ.get(name, default))


def main():
    out = {}
    ns = [int(x) for x in os.environ.get("SIGIL_REDTEAM_NS", "4,7,10").split(",")]
    steps = _int("SIGIL_REDTEAM_STEPS", 150)
    budget = float(os.environ.get("SIGIL_REDTEAM_TIME", "0"))

    # 1. Schedule explorer (S1, S2), honest minority within the fault bound.
    explorer = {}
    for n in ns:
        for store in (False, True) if n == 4 else (False,):
            label = f"n{n}" + ("_store" if store else "")
            if budget:
                deadline, start_seed, agg, viol = time.time() + budget / len(ns), 0, None, None
                while time.time() < deadline and viol is None:
                    viol, stats = model.explore(5, steps, n=n, use_store=store, start_seed=start_seed)
                    start_seed += 5
                    if agg is None:
                        agg = stats
                    else:
                        for k, v in stats.items():
                            agg[k] += v
                explorer[label] = {"violation": viol, "stats": agg}
            else:
                seeds = _int("SIGIL_REDTEAM_SEEDS", 60)
                viol, stats = model.explore(seeds, steps, n=n, use_store=store)
                explorer[label] = {"violation": viol, "stats": stats}
    out["schedule_explorer"] = explorer

    if os.environ.get("SIGIL_REDTEAM_BEYOND") == "1":
        viol, stats = model.explore(50, steps, n=4, byz=2, allow_rotation=False)
        out["beyond_f"] = {"violation": viol, "stats": stats}

    # 2. Payment-level conservation fuzzer (S3, S4, S5).
    cv, cstats = conserve.run(_int("SIGIL_REDTEAM_CONSERVE_SEEDS", 20),
                              _int("SIGIL_REDTEAM_CONSERVE_STEPS", 60))
    out["conservation_fuzzer"] = {"violation": cv, "stats": cstats}

    # 3. Resource-exhaustion probes.
    out["resources"] = {
        "spend_cpu": resources.spend_cpu_amplification(),
        "gossip_store": resources.gossip_store_growth(),
        "storage_per_spend": resources.storage_per_spend(),
    }

    print(json.dumps(out, indent=2))
    # Non-zero exit if any safety invariant broke within the fault bound.
    broke = any(v["violation"] for v in explorer.values()) or cv is not None
    return 1 if broke else 0


if __name__ == "__main__":
    raise SystemExit(main())
