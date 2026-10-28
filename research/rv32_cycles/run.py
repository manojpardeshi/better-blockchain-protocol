"""Measure the Sigil step relation as an RV32IM guest program.

1. Builds real histories with ``sigil.Wallet`` and turns chosen transitions
   into step witnesses (``research.pcd.witness_for`` + the parents'
   statements), with the statement digest the Python reference computes.
2. Builds the bare-metal guest (guest/, target riscv32im-unknown-none-elf)
   and the instruction-counting emulator (emu/).
3. Runs the guest on every witness, checks that it computes the *same*
   statement digest as research/pcd.py, and reports instruction counts by
   category (parse / canonical encoding / BLAKE2b / Ed25519 / logic).

Usage::

    python3 -m research.rv32_cycles.run [--json research/results/rv32_cycles.json]

Needs a Rust toolchain with the riscv32im-unknown-none-elf target
(``rustup target add riscv32im-unknown-none-elf``).
"""

import argparse
import json
import os
import re
import subprocess
import sys

from research._compat import ensure_wallet_signs_expiry
from research.pcd import STEP_ID, IdealBackend, prove_history, step, witness_for
from sigil import Network, Wallet
from sigil.swap import atomic_swap

HERE = os.path.dirname(os.path.abspath(__file__))
ensure_wallet_signs_expiry()


def witness_json(dossier, tid, registry, proofs) -> tuple[dict, str]:
    w = witness_for(dossier, tid, registry)
    children = {r["tx"]: proofs[r["tx"]].statement for r in w.body["inputs"]}
    expected = step(w, children).digest()
    obj = {
        "step_id": STEP_ID, "tid": tid, "header": w.header, "body": w.body, "unlocks": w.unlocks,
        "inputs": [{"parcel": i.parcel, "seal": i.seal, "charter": i.charter} for i in w.inputs],
        "excluded": sorted(w.excluded),
        "children": {t: st.to_json() for t, st in children.items()},
    }
    return obj, expected


def scenarios() -> list:
    """(name, inputs, n, witness, expected digest) for representative transitions."""
    out = []
    for n in (4, 7, 16, 31):
        net = Network()
        X, Y = net.create_constellation("orion", n), net.create_constellation("lyra", n)
        alice, bob, carol = Wallet("alice", net, X), Wallet("bob", net, Y), Wallet("carol", net, X)
        usd = alice.issue("USD", 1_000)
        cases = {"genesis": usd, "payment": alice.pay(bob, usd, 300)}
        if n == 4:
            for _ in range(4):
                alice.pay(carol, usd, 10)
            carol_extra = bob.pay(carol, usd, 5)
            cases["merge5"] = carol.pay(alice, usd, 45, home=Y)
            gold = bob.issue("GOLD", 50)
            cases["swap"] = atomic_swap(alice, usd, 100, bob, gold, 5)
            del carol_extra
        for name, tid in cases.items():
            holder = alice if name in ("genesis", "merge5", "swap") else bob
            d = holder.dossier.ancestry([tid])
            proofs = prove_history(IdealBackend(), d, [tid], net.registry)
            obj, expected = witness_json(d, tid, net.registry, proofs)
            out.append({"name": f"{name}-n{n}", "inputs": len(obj["inputs"]), "n": n,
                        "votes": sum(len(i["seal"]["votes"]) for i in obj["inputs"]),
                        "witness": obj, "expected": expected})
    return out


def cargo_build(crate: str, nightly: bool = False, target: str | None = None) -> None:
    cmd = ["cargo"] + (["+nightly"] if nightly else []) + ["build", "--release", "--quiet"]
    if target:
        cmd += ["--target", target]
    subprocess.run(cmd, cwd=os.path.join(HERE, crate), check=True)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="write results here")
    args = ap.parse_args(argv)
    wdir = os.path.join(HERE, "witnesses")
    os.makedirs(wdir, exist_ok=True)
    cargo_build("emu")
    cargo_build("guest", target="riscv32im-unknown-none-elf")
    emu = os.path.join(HERE, "emu", "target", "release", "rv32-count")
    elf = os.path.join(HERE, "guest", "target", "riscv32im-unknown-none-elf", "release", "sigil-step-guest")
    rows = []
    for sc in scenarios():
        path = os.path.join(wdir, sc["name"] + ".json")
        with open(path, "w") as f:
            json.dump(sc["witness"], f, sort_keys=True)
        r = subprocess.run([emu, elf, path], capture_output=True, text=True)
        out = r.stdout
        m = re.search(r"STATEMENT ([0-9a-f]{64})", out)
        prof = dict((k, int(v)) for k, v in re.findall(r"(\w+)=(\d+)", out.split("PROFILE", 1)[-1]))
        total = int(re.search(r"RETIRED (\d+)", out).group(1))
        ok = bool(m) and m.group(1) == sc["expected"]
        rows.append({"name": sc["name"], "inputs": sc["inputs"], "n": sc["n"], "votes": sc["votes"],
                     "witness_bytes": os.path.getsize(path), "instructions": total,
                     "digest_matches_python": ok, **prof})
        if not ok:
            print(f"MISMATCH {sc['name']}: {out} {r.stderr}", file=sys.stderr)
    cols = ["name", "inputs", "votes", "witness_bytes", "instructions", "parse", "encode", "blake2b",
            "ed25519", "logic", "hashes", "signatures", "digest_matches_python"]
    print("| " + " | ".join(cols) + " |\n|" + "---|" * len(cols))
    for row in rows:
        print("| " + " | ".join(f"{row[c]:,}" if isinstance(row[c], int) and not isinstance(row[c], bool)
                                else str(row[c]) for c in cols) + " |")
    sigs = [r for r in rows if r["signatures"]]
    if sigs:
        per_sig = sum(r["ed25519"] for r in sigs) / sum(r["signatures"] for r in sigs)
        per_hash = sum(r["blake2b"] for r in rows) / sum(r["hashes"] for r in rows)
        print(f"\nmean Ed25519 verify: {per_sig:,.0f} instructions; mean BLAKE2b call: {per_hash:,.0f}")
    if args.json:
        with open(args.json, "w") as f:
            json.dump(rows, f, indent=1)
    return rows


if __name__ == "__main__":
    main()
