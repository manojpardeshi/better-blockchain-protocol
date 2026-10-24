#!/usr/bin/env python3
"""Interop test: Rust witnesses driven by the *Python* wallet over the v0 wire protocol.

    cargo build --release --manifest-path rust/Cargo.toml
    python3 bench/interop.py [--keep]

Starts three constellations of witness processes from files written by the Python daemon
(``sigil.witnessd keygen`` / ``genesis``):

* X: 4 Rust witnesses, Y: 4 Rust witnesses,
* Z: 2 Rust + 2 Python witnesses (seals mix votes from both implementations),

then runs, through ``sigil.server.RemoteNetwork`` and ``sigil.wallet.Wallet``: issue, pay
(across constellations), receive with deep confirmation, an atomic swap with inputs in two
constellations, a double spend (conflict carrying the first vote; no second seal), recovery
of a parcel from a dead swap via a death proof (RELEASE), expiry of owner authorisations,
time locks, and a SIGKILL of a Rust witness mid-payments followed by a restart on the same
store (it returns the same vote byte for byte and refuses the conflicting spend).

Exits non-zero on the first failure.
"""

import argparse
import os
import shutil
import signal
import sys
import tempfile
import threading
import time
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import RUST_BIN, Cluster, manual_spend  # noqa: E402

from sigil import Wallet, locks, model  # noqa: E402
from sigil.server import RemoteNetwork, RemoteWitness  # noqa: E402
from sigil.swap import atomic_swap, propose_swap  # noqa: E402
from sigil.validate import InvalidDossier  # noqa: E402
from sigil.wallet import SealFailed, request_seal  # noqa: E402
from sigil.witness import Conflict, Rejected  # noqa: E402

RESULTS = []


def check(name):
    def wrap(fn):
        def run(*a, **kw):
            t = time.perf_counter()
            try:
                fn(*a, **kw)
            except Exception:
                RESULTS.append((name, False, time.perf_counter() - t))
                print(f"FAIL  {name}")
                traceback.print_exc()
                raise
            RESULTS.append((name, True, time.perf_counter() - t))
            print(f"ok    {name}  ({time.perf_counter() - t:.2f}s)")
        return run
    return wrap


class Interop:
    def __init__(self, cluster: Cluster, X: str, Y: str, Z: str):
        self.c, self.X, self.Y, self.Z = cluster, X, Y, Z
        self.W = Wallet

    def net(self) -> RemoteNetwork:
        return RemoteNetwork(self.c.directory(), timeout=5)

    @check("charters and info served by Rust witnesses verify against the cids")
    def charters(self):
        net = self.net()
        for cid in (self.X, self.Y, self.Z):
            assert len(net.registry.latest(cid)["witnesses"]) == 4
            ws = net.witnesses(cid)
            assert len(ws) == 4 and all(w.cid == cid and w.version == 0 and w.stamps is None for w in ws)

    @check("issue, pay across constellations, deep confirmation, mixed Rust+Python seals")
    def payments(self):
        net = self.net()
        alice, bob, carol = self.W("alice", net, self.X), self.W("bob", net, self.Y), self.W("carol", net, self.Z)
        usd = alice.issue("USD", 1_000)
        alice.pay(bob, usd, 300)                                  # sealed by Rust witnesses of X
        assert (alice.balance(usd), bob.balance(usd)) == (700, 300)
        tid = bob.pay(carol, usd, 120)                            # sealed by Rust witnesses of Y
        assert carol.balance(usd) == 120
        tid2 = carol.pay(alice, usd, 20)                          # sealed by mixed Rust+Python Z
        seal = next(s for s in alice.dossier.seals.values() if s["tid"] == tid2)
        rust_pks = {RemoteWitness(self.c.url(i)).pk for i, w in enumerate(self.c.witnesses)
                    if w["cid"] == self.Z and w["kind"] == "rust"}
        assert {v["witness"] for v in seal["votes"]} & rust_pks, "mixed seal has Rust votes"
        assert {v["witness"] for v in seal["votes"]} - rust_pks, "mixed seal has Python votes"
        # A fresh holder verifies the whole history and deep-confirms every input against STATUS.
        erin = self.W("erin", net, self.Y, deep_threshold=1)
        carol.pay(erin, usd, 10)
        assert erin.balance(usd) == 10 and len(erin._confirmed) >= 3

    @check("atomic swap with inputs in two Rust constellations")
    def swap(self):
        net = self.net()
        alice, bob = self.W("alice", net, self.X), self.W("bob", net, self.Y)
        usd, gold = alice.issue("USD", 1_000), bob.issue("GOLD", 10)
        atomic_swap(alice, usd, 100, bob, gold, 2)
        assert (alice.balance(usd), alice.balance(gold)) == (900, 2)
        assert (bob.balance(usd), bob.balance(gold)) == (100, 8)

    @check("double spend: conflict carries the first vote, the second spend never seals")
    def double_spend(self):
        net = self.net()
        carol, bob, alice = self.W("carol", net, self.X), self.W("bob", net, self.X), self.W("alice", net, self.X)
        coin = carol.issue("C", 5)
        refs, _ = carol.select(coin, 5)
        b, a = bob.address(), alice.address()
        *_, r1 = manual_spend(carol, refs, [model.parcel(self.X, coin, 5, b["lock"], b["salt"])])
        *_, r2 = manual_spend(carol, refs, [model.parcel(self.X, coin, 5, a["lock"], a["salt"])])
        seal = request_seal(net, r1[0])
        w0 = net.witnesses(self.X)[0]
        try:
            w0.spend(r2[0])
            raise AssertionError("conflicting spend was accepted")
        except Conflict as e:
            first = next(v for v in seal["votes"] if v["witness"] == w0.pk)
            assert e.vote["sig"] == first["sig"] and e.vote["tid"] == seal["tid"]
        try:
            request_seal(net, r2[0])
            raise AssertionError("double spend sealed")
        except SealFailed as e:
            assert len(e.conflicts) == 4

    @check("release: recover a parcel from a dead swap with a death proof, then spend at gen 1")
    def release(self):
        net = self.net()
        alice, mallory, bob = self.W("alice", net, self.X), self.W("mallory", net, self.Y), self.W("bob", net, self.X)
        usd, gold = alice.issue("USD", 100), mallory.issue("GOLD", 10)
        header, body, _ = propose_swap(alice, usd, 100, mallory, gold, 10)
        unlocks = {**alice.authorise(header, body), **mallory.authorise(header, body)}
        me = mallory.address()
        *_, betrayal = manual_spend(mallory, [body["inputs"][1]], [model.parcel(self.Y, gold, 10, me["lock"], me["salt"])])
        betrayal_seal = request_seal(net, betrayal[0])  # mallory seals her input elsewhere first
        try:
            alice.seal(header, body, unlocks)
            raise AssertionError("dead swap sealed")
        except SealFailed:
            pass
        a_sigil = header["inputs"][0][0]
        assert all(w.status(a_sigil)["tid"] == model.transition_id(header) for w in net.witnesses(self.X))
        # A forged proof (a seal from Y, for another sigil, named against alice's input) is refused.
        p = alice.dossier.output(body["inputs"][0])
        bad = {"kind": "seal", "sigil": a_sigil, "gen": 0, "parcel": {k: p[k] for k in ("home", "lock", "salt")},
               "seal": betrayal_seal}
        try:
            net.witnesses(self.X)[0].release(a_sigil, bad)
            raise AssertionError("bogus death proof accepted")
        except Rejected:
            pass
        assert len(alice.abort(header)) == 1           # every Rust witness of X accepts the real proof
        assert all(w.status(a_sigil)["gen"] == 1 for w in net.witnesses(self.X))
        alice.pay(bob, usd, 100)                       # spent again, at generation 1
        assert bob.balance(usd) == 100

    @check("owner authorisations expire; time locks use the witness clock")
    def expiry_and_timelocks(self):
        net = self.net()
        alice, bob = self.W("alice", net, self.X), self.W("bob", net, self.X)
        usd = alice.issue("USD", 10)
        refs, _ = alice.select(usd, 10)
        b = bob.address()
        *_, reqs = manual_spend(alice, refs, [model.parcel(self.X, usd, 10, b["lock"], b["salt"])],
                                expires=int(time.time()) - 5)
        for w in net.witnesses(self.X):
            try:
                w.spend(reqs[0])
                raise AssertionError("expired authorisation bound a sigil")
            except Rejected as e:
                assert "expired" in str(e)
        # A time-locked parcel: all(sig, after(t)) with t in the future, then in the past.
        kp = alice.fresh_key()
        for t, ok in ((int(time.time()) + 3600, False), (int(time.time()) - 3600, True)):
            lock = locks.all_of(locks.sig(kp.pk), locks.after(t))
            p = {"home": self.X, "lock": lock, "salt": os.urandom(16).hex()}
            s = model.sigil_of(p)
            hdr = model.header([[s, 0]], model.body([model.ref("0" * 64, 0)], [model.parcel(self.X, "a", 1, lock, "bb")]))
            tid = model.transition_id(hdr)
            exp = int(time.time()) + 600
            u = locks.empty_unlock(exp)
            u["sigs"][kp.pk] = locks.sign_unlock(kp, s, tid, exp)
            req = dict(p, sigil=s, header=hdr, unlock=u)
            got = 0
            for w in net.witnesses(self.X):
                try:
                    w.spend(req)
                    got += 1
                except Rejected as e:
                    assert "not satisfied now" in str(e)
            assert got == (4 if ok else 0), (t, ok, got)

    @check("SIGKILL a Rust witness mid-payments, restart on the same store: votes remembered")
    def crash_restart(self):
        c = self.c
        victim = next(i for i, w in enumerate(c.witnesses) if w["cid"] == self.X and w["kind"] == "rust")
        net = self.net()
        alice, bob, carol = self.W("alice", net, self.X), self.W("bob", net, self.X), self.W("carol", net, self.X)
        usd = alice.issue("USD", 1_000)
        coin = carol.issue("C", 5)
        refs, _ = carol.select(coin, 5)
        b, a = bob.address(), alice.address()
        *_, r1 = manual_spend(carol, refs, [model.parcel(self.X, coin, 5, b["lock"], b["salt"])])
        *_, r2 = manual_spend(carol, refs, [model.parcel(self.X, coin, 5, a["lock"], a["salt"])])
        client = RemoteWitness(c.url(victim), timeout=3)
        vote = client.spend(r1[0])

        started, killed = threading.Event(), threading.Event()

        def killer():
            started.wait(30)
            c.kill(victim, signal.SIGKILL)
            killed.set()

        t = threading.Thread(target=killer, daemon=True)
        t.start()
        after = 0
        for i in range(60):
            alice.pay(bob, usd, 1)                 # must never fail: f = 1 is tolerated
            bob.pay(alice, usd, 1)
            if i == 2:
                started.set()
            if killed.is_set():
                after += 1
                if after >= 3:
                    break
        t.join(10)
        assert after >= 3, "payments did not continue with a witness down"
        try:
            client.status(vote["sigil"])
            raise AssertionError("victim still up")
        except Rejected:
            pass
        c.start(victim)
        c.wait_ready(victim)
        assert client.spend(r1[0]) == vote, "same vote, byte for byte"
        try:
            client.spend(r2[0])
            raise AssertionError("conflicting spend accepted after restart")
        except Conflict as e:
            assert e.vote == vote
        remembered = 0
        for seal in list(alice.dossier.seals.values()) + list(bob.dossier.seals.values()):
            for v in seal["votes"]:
                if v["witness"] == client.pk:
                    held = {(x["tid"], x["sig"]) for x in client.status(seal["sigil"])["votes"]}
                    assert (seal["tid"], v["sig"]) in held
                    remembered += 1
        assert remembered >= 3, remembered
        alice.pay(bob, usd, 5)                     # and it votes again

    @check("malformed and hostile requests get the reference's error kinds")
    def errors(self):
        import json
        import urllib.error
        import urllib.request
        url = self.c.url(0)

        def post(path, data: bytes):
            req = urllib.request.Request(url + path, data=data, method="POST", headers={"Content-Type": "application/json"})
            try:
                with urllib.request.urlopen(req, timeout=5) as r:
                    return r.status, json.loads(r.read())
            except urllib.error.HTTPError as e:
                return e.code, json.loads(e.read())

        assert post("/v0/spend", b"{}")[0] == 400
        assert post("/v0/spend", b"not json")[0] == 400
        assert post("/v0/spend", b'{"request": 5}') == (403, {"error": "rejected", "message": "malformed request", "vote": None})
        assert post("/v0/nope", b"{}")[0] == 400
        assert post("/v0/status", b'{"sigil": "x"}') == (200, {"ok": {"gen": 0, "tid": None, "votes": []}})
        assert post("/v0/release", b'{"sigil": "x", "proof": {}}')[0] == 403
        assert post("/v0/spend", b'{"request": {}, "pad": "' + b"x" * (1 << 20) + b'"}')[0] == 400
        try:
            RemoteWitness(url).sell_stamp(12345)
            raise AssertionError("stamp sold")
        except Rejected:
            pass

    def run_all(self):
        for t in (self.charters, self.payments, self.swap, self.double_spend, self.release,
                  self.expiry_and_timelocks, self.crash_restart, self.errors):
            t()


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true", help="keep the cluster directory")
    args = ap.parse_args(argv)
    if not os.path.exists(RUST_BIN):
        raise SystemExit(f"{RUST_BIN} not found: cargo build --release --manifest-path rust/Cargo.toml")
    tmp = tempfile.mkdtemp(prefix="sigil-interop-")
    c = Cluster(tmp)
    try:
        X = c.create("orion", ["rust"] * 4)
        Y = c.create("lyra", ["rust"] * 4)
        Z = c.create("vega", ["rust", "python", "rust", "python"])
        c.start_all()
        Interop(c, X, Y, Z).run_all()
    finally:
        c.stop_all(signal.SIGTERM)
        if args.keep:
            print("cluster kept in", tmp)
        else:
            shutil.rmtree(tmp, ignore_errors=True)
    print(f"\n{sum(ok for _, ok, _ in RESULTS)}/{len(RESULTS)} interop checks passed")


if __name__ == "__main__":
    main()
