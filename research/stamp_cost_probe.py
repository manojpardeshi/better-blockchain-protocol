#!/usr/bin/env python3
"""Measure local Python witness stamp operations with a durable SQLite store.

This is an operation probe, not a price estimator or a network benchmark. RSA key
generation, request construction and client blinding are outside timed phases.
"""

import argparse
import json
import os
import platform
import secrets
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sigil import model  # noqa: E402
from sigil.charter import Registry, charter_body, constellation_id  # noqa: E402
from sigil.crypto import KeyPair  # noqa: E402
from sigil.locks import empty_unlock, sig, sign_unlock  # noqa: E402
from sigil.stamps import StampMint, blind, unblind, verify_stamp  # noqa: E402
from sigil.store import WitnessStore  # noqa: E402
from sigil.witness import Rejected, Witness  # noqa: E402


def _request(cid: str, owner: KeyPair, index: int) -> dict:
    lock = sig(owner.pk)
    salt = f"cost-probe-{index:08d}"
    sigil = model.sigil_of({"home": cid, "lock": lock, "salt": salt})
    header = {"inputs": [[sigil, 0]], "body": "b" * 64}
    tid = model.transition_id(header)
    expires = int(time.time()) + 86400
    unlock = empty_unlock(expires)
    unlock["sigs"][owner.pk] = sign_unlock(owner, sigil, tid, expires)
    return {"sigil": sigil, "header": header, "home": cid, "lock": lock,
            "salt": salt, "unlock": unlock}


def _store_snapshot(store: WitnessStore) -> dict:
    # Checkpointing is outside the timed operation. The resulting DB file is a
    # useful footprint, not the bytes written by the SQLite WAL or filesystem.
    busy, _, _ = store.db.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchone()
    if busy:
        raise RuntimeError("SQLite checkpoint was busy")
    page_count = store.db.execute("PRAGMA page_count").fetchone()[0]
    page_size = store.db.execute("PRAGMA page_size").fetchone()[0]
    rows = store.db.execute(
        "SELECT kind, COUNT(*), SUM(LENGTH(CAST(kind AS BLOB)) + "
        "LENGTH(CAST(key AS BLOB)) + LENGTH(CAST(value AS BLOB))) "
        "FROM log GROUP BY kind"
    ).fetchall()
    return {"db_bytes": page_count * page_size,
            "log_payload_bytes": sum(row[2] for row in rows),
            "rows_by_kind": {kind: count for kind, count, _ in rows}}


def _phase(store: WitnessStore, operations: int, fn) -> dict:
    before = _store_snapshot(store)
    cpu_start = time.process_time()
    wall_start = time.perf_counter()
    fn()
    wall_seconds = time.perf_counter() - wall_start
    cpu_seconds = time.process_time() - cpu_start
    after = _store_snapshot(store)
    return {"operations": operations, "wall_seconds": wall_seconds,
            "cpu_seconds": cpu_seconds,
            "wall_ms_per_operation": wall_seconds * 1000 / operations,
            "cpu_ms_per_operation": cpu_seconds * 1000 / operations,
            "db_bytes_delta": after["db_bytes"] - before["db_bytes"],
            "log_payload_bytes_delta": after["log_payload_bytes"] - before["log_payload_bytes"],
            "rows_delta_by_kind": {kind: after["rows_by_kind"].get(kind, 0) -
                                   before["rows_by_kind"].get(kind, 0)
                                   for kind in sorted(set(before["rows_by_kind"]) |
                                                      set(after["rows_by_kind"]))}}


def _check_rows(phase: dict, *, stamps: int, records: int) -> None:
    changes = phase["rows_delta_by_kind"]
    if changes.get("stamp", 0) != stamps or changes.get("record", 0) != records:
        raise RuntimeError(f"unexpected durable rows: {changes!r}")


def run(count: int = 100, stamp_bits: int = 2048) -> dict:
    if count <= 0:
        raise ValueError("count must be positive")
    if stamp_bits not in (1024, 2048, 3072, 4096):
        raise ValueError("stamp_bits must be one of 1024, 2048, 3072, 4096")

    witness_key = KeyPair.from_seed(b"stamp-cost-probe-witness")
    owner = KeyPair.from_seed(b"stamp-cost-probe-owner")
    body = charter_body("cost-probe", 0, [witness_key.pk], None)
    cid = constellation_id(body)
    registry = Registry()
    registry.add_chain(cid, [{"body": body, "sigs": {}}])
    mint = StampMint(stamp_bits)
    # Setup, including key generation and initial membership write, is excluded.
    with tempfile.TemporaryDirectory(prefix="sigil-stamp-cost-") as tmp:
        store = WitnessStore(os.path.join(tmp, "w.db"))
        try:
            witness = Witness(witness_key, registry, lambda: int(time.time()),
                              stamp_mint=mint, store=store)
            witness.join(cid, 0)
            prepared = []
            for _ in range(2 * count):
                serial = secrets.token_hex(16)
                blinded, factor = blind(mint.public, serial)
                prepared.append((serial, blinded, factor))
            signatures = []

            def sell():
                for _, blinded, _ in prepared:
                    signatures.append(witness.sell_stamp(blinded))

            sale = _phase(store, len(prepared), sell)
            _check_rows(sale, stamps=0, records=0)
            stamps = []
            for (serial, _, factor), signed in zip(prepared, signatures):
                stamp = {"serial": serial,
                         "sig": format(unblind(mint.public, signed, factor), "x")}
                if not verify_stamp(mint.public, stamp):
                    raise RuntimeError("sale returned an invalid stamp")
                stamps.append(stamp)

            accepted_requests = [{**_request(cid, owner, i), "stamp": stamps[i]}
                                 for i in range(count)]
            rejected_requests = [{**_request(cid, owner, count + i),
                                  "home": "0" * 64, "stamp": stamps[count + i]}
                                 for i in range(count)]

            def accept():
                for req in accepted_requests:
                    vote = witness.spend(req)
                    if vote.get("sigil") != req["sigil"]:
                        raise RuntimeError("accepted SPEND returned the wrong vote")

            accepted = _phase(store, count, accept)
            _check_rows(accepted, stamps=count, records=count)

            def reject_valid_stamp():
                for req in rejected_requests:
                    try:
                        witness.spend(req)
                    except Rejected as exc:
                        if str(exc) != "sigil does not live here":
                            raise RuntimeError(f"unexpected rejection: {exc}") from exc
                    else:
                        raise RuntimeError("wrong-home SPEND was accepted")

            rejected = _phase(store, count, reject_valid_stamp)
            _check_rows(rejected, stamps=count, records=0)

            def reject_replay():
                for req in accepted_requests:
                    try:
                        witness.spend(req)
                    except Rejected as exc:
                        if str(exc) != "missing or spent stamp":
                            raise RuntimeError(f"unexpected replay rejection: {exc}") from exc
                    else:
                        raise RuntimeError("replayed stamp was accepted")

            replayed = _phase(store, count, reject_replay)
            _check_rows(replayed, stamps=0, records=0)
            return {"probe": "python_witness_stamp_cost", "count_per_spend_path": count,
                    "stamp_bits": stamp_bits, "python": platform.python_version(),
                    "platform": platform.platform(), "phases": {
                        "sale_sign": sale, "spend_accepted": accepted,
                        "spend_rejected_valid_stamp": rejected,
                        "spend_rejected_replay": replayed}}
        finally:
            store.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=100, help="operations per SPEND path")
    parser.add_argument("--stamp-bits", type=int, default=2048,
                        choices=(1024, 2048, 3072, 4096))
    args = parser.parse_args()
    if args.count <= 0:
        parser.error("--count must be positive")
    print(json.dumps(run(args.count, args.stamp_bits), sort_keys=True))


if __name__ == "__main__":
    main()
