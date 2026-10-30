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
        return RemoteNetwork(self.c.directory([self.X, self.Y, self.Z]), timeout=5)

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

    # ------------------------------------------------------------ rotation, stamps, gossip

    def admin(self) -> dict:
        """Witness flags enabling the rotation calls with this cluster's admin token."""
        if not hasattr(self, "_token"):
            self._token = os.urandom(16).hex()
            self._token_file = os.path.join(self.c.dir, "admin.token")
            with open(self._token_file, "w") as f:
                f.write(self._token + "\n")
        args = ["--admin-token", self._token_file]
        return {"rust": args, "python": args}

    def constellation(self, name: str, kinds: list, extra: dict | None = None) -> tuple[str, list]:
        """Create and start a constellation; returns ``(cid, witness indices)``."""
        args = self.admin()
        for k, v in (extra or {}).items():
            args = dict(args, **{k: args.get(k, []) + v})
        cid = self.c.create(name, kinds, args)
        idx = self.c.indices(cid)
        self.c.start_all(idx)
        return cid, idx

    def new_members(self, cid: str, kinds: list, keys: list | None = None) -> list:
        """Start witnesses that wait for ADOPT into the next version of ``cid``; returns their URLs."""
        idx = self.c.add_members(cid, kinds, self.admin(), keys)
        self.c.start_all(idx)
        for i in idx:
            self.c.witnesses[i]["pending"] = False   # in the directory from now on
        return [self.c.url(i) for i in idx]

    @check("rotation over HTTP: old Rust members freeze, new Rust+Python members (one re-used key) adopt")
    def rotation(self):
        c = self.c
        R, old = self.constellation("rotor", ["rust"] * 4)
        old_urls = [c.url(i) for i in old]
        net = RemoteNetwork({R: old_urls}, timeout=10)
        alice, bob, carol = self.W("alice", net, R), self.W("bob", net, R), self.W("carol", net, R)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 30)
        coin = carol.issue("C", 5)
        refs, _ = carol.select(coin, 5)
        b, a = bob.address(), alice.address()
        *_, r1 = manual_spend(carol, refs, [model.parcel(R, coin, 5, b["lock"], b["salt"])])
        *_, r2 = manual_spend(carol, refs, [model.parcel(R, coin, 5, a["lock"], a["salt"])])
        request_seal(net, r1[0])
        # Without the admin token nobody can freeze a witness.
        cur = net.registry.latest(R)
        from sigil.charter import charter_body, charter_hash
        probe = charter_body(cur["name"], 1, ["aa" * 32], charter_hash(cur))
        for token in (None, "wrong"):
            try:
                RemoteWitness(old_urls[0], admin_token=token).freeze(probe)
                raise AssertionError("freeze without the admin token")
            except Rejected as e:
                assert "admin token" in str(e), e
        assert not any(RemoteWitness(u)._get("info")["frozen"] for u in old_urls)

        new_urls = self.new_members(R, ["rust", "rust", "python", "python"], keys=[c.witnesses[old[0]]["key"], None, None, None])
        assert all(RemoteWitness(u).cid is None for u in new_urls), "new members wait for ADOPT"
        assert net.rotate(R, new_urls, self._token) == 1
        c.write_chain(R, net.registry.chain(R))
        for u in old_urls:
            w = RemoteWitness(u)
            assert w._get("info")["frozen"] and w.version == 0
            try:
                w.spend(r1[0])
                raise AssertionError("a frozen witness voted")
            except Rejected as e:
                assert "not active" in str(e)
        ws = net.witnesses(R)
        assert [w.url for w in ws] == new_urls and all(w.version == 1 for w in ws)
        for w in ws:                               # the binding was inherited by every new member
            v = w.spend(r1[0])
            assert v["version"] == 1 and v["tid"] == model.transition_id(r1[0]["header"])
            try:
                w.spend(r2[0])
                raise AssertionError("a new member voted a second transition at an inherited binding")
            except Conflict:
                pass
        # The re-used key brought its own vote along: both of its votes on the sigil are for r1.
        reused = ws[0].status(r1[0]["sigil"])["votes"]
        assert {v["version"] for v in reused} == {0, 1} and len({v["tid"] for v in reused}) == 1
        bob.pay(alice, usd, 10)                    # payments continue under version 1
        erin = self.W("erin", RemoteNetwork({R: new_urls}, timeout=10), R, deep_threshold=1)
        alice.pay(erin, usd, 5)                    # history sealed by v0 and v1, deep-confirmed by v1
        assert erin.balance(usd) == 5 and len(erin._confirmed) >= 2
        # A restarted old Rust witness is still frozen, for that successor only; a restarted new
        # member still serves version 1.
        for i in (old[1], c.indices(R)[-4]):
            c.kill(i, signal.SIGKILL)
            c.start(i)
            c.wait_ready(i)
        w = RemoteWitness(c.url(old[1]), admin_token=self._token)
        assert w._get("info")["frozen"]
        try:
            w.freeze(dict(probe, version=1))
            raise AssertionError("froze for a second successor after a restart")
        except Rejected as e:
            assert "different successor" in str(e)
        assert RemoteWitness(new_urls[0]).version == 1
        alice.pay(bob, usd, 1)

    def _regression(self, sealed: str, old_kinds: list, new_kinds: list):
        """tests/test_conformance.py RotationRegressionTests._scenario, over HTTP."""
        from sigil.crypto import KeyPair
        from sigil.proofs import verify_seal
        X, old = self.constellation(f"reg-{sealed.lower()}", old_kinds)
        net = RemoteNetwork({X: [self.c.url(i) for i in old]}, timeout=10)
        owner = KeyPair.generate()
        exp = int(time.time()) + 600

        def mk(salt):
            p = model.parcel(X, "x", 1, locks.sig(owner.pk), salt)
            return p, model.sigil_of(p)

        ps, s = mk(os.urandom(8).hex())
        px, x = mk(os.urandom(8).hex())
        tgt = lambda p: {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}  # noqa: E731
        hdr = lambda inputs, tag: {"inputs": [list(i) for i in inputs], "body": tag * 64}  # noqa: E731

        def req(h, sigil, p):
            u = locks.empty_unlock(exp)
            u["sigs"][owner.pk] = locks.sign_unlock(owner, sigil, model.transition_id(h), exp)
            return {"sigil": sigil, "header": h, "home": X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

        Ty, Tb, Ta, Tg = hdr([(x, 0)], "1"), hdr([(s, 0), (x, 0)], "2"), hdr([(s, 0)], "3"), hdr([(s, 1)], "4")
        k = net.witnesses(X)
        seal_y = model.seal_from_votes([w.spend(req(Ty, x, px)) for w in k])
        quorum_tx, single_tx = (Tb, Ta) if sealed == "Tb" else (Ta, Tb)
        seal_q = model.seal_from_votes([w.spend(req(quorum_tx, s, ps)) for w in k[:3]])
        k[3].spend(req(single_tx, s, ps))
        dp_b = {"kind": "seal", "sigil": x, "gen": 0, "parcel": tgt(px), "seal": seal_y}
        for w in (k[:3] if sealed == "Tb" else k[3:]):
            w.release(s, dp_b)
        assert net.rotate(X, self.new_members(X, new_kinds), self._token) == 1

        def try_seal(h):
            votes = []
            for w in net.witnesses(X):
                try:
                    votes.append(w.spend(req(h, s, ps)))
                except Rejected:  # includes Conflict
                    pass
            seal = model.seal_from_votes(votes) if votes else None
            return seal if seal and verify_seal(seal, net.registry) else None

        def release_all(proof):
            for w in net.witnesses(X):
                try:
                    w.release(s, proof)
                except Rejected:
                    pass

        return net, X, s, ps, tgt, (Ta, Tg), seal_q, try_seal, release_all

    @check("rotation regression 1 (Rust witnesses): ADOPT does not reopen a consumed generation")
    def regression_reopen(self):
        net, X, s, ps, tgt, (Ta, Tg), seal_b, try_seal, release_all = self._regression("Tb", ["rust"] * 4, ["rust"] * 4)
        for w in net.witnesses(X):
            assert w.status(s)["tid"] == "!contested", w
        assert try_seal(Ta) is None, "the new charter sealed a second tid at (s,0)"
        release_all({"kind": "seal", "sigil": s, "gen": 0, "parcel": tgt(ps), "seal": seal_b})
        assert all(w.status(s) == {"gen": 1, "tid": None, "votes": []} for w in net.witnesses(X))
        assert try_seal(Tg) is not None
        assert try_seal(Ta) is None

    @check("rotation regression 2 (mixed Rust+Python, both versions): ADOPT keeps a sealed sibling")
    def regression_sibling(self):
        net, X, s, ps, tgt, (Ta, Tg), seal_a, try_seal, release_all = self._regression(
            "Ta", ["rust", "python", "rust", "python"], ["python", "rust", "rust", "python"])
        assert try_seal(Tg) is None
        release_all({"kind": "seal", "sigil": s, "gen": 0, "parcel": tgt(ps), "seal": seal_a})
        assert try_seal(Tg) is None, "s was consumed by Ta and again by Tg"
        assert all(w.status(s)["tid"] == "!contested" for w in net.witnesses(X))

    @check("stamps: Rust (+Python) witnesses sell blind stamps, redeem each once, remember across restarts")
    def stamps(self):
        from sigil.stamps import buy_stamp
        c = self.c
        S, idx = self.constellation("stamped", ["rust", "python", "rust", "rust"], {"rust": ["--stamps"], "python": ["--stamps"]})
        net = RemoteNetwork({S: [c.url(i) for i in idx]}, timeout=10)
        ws = net.witnesses(S)
        assert all(w.stamps is not None for w in ws)
        alice, bob = self.W("alice", net, S), self.W("bob", net, S)
        usd = alice.issue("USD", 50)
        refs, _ = alice.select(usd, 50)
        b = bob.address()
        *_, reqs = manual_spend(alice, refs, [model.parcel(S, usd, 50, b["lock"], b["salt"])])
        rust = ws[0]
        try:
            rust.spend(reqs[0])
            raise AssertionError("spent without a stamp")
        except Rejected as e:
            assert "stamp" in str(e)
        st = buy_stamp(rust.stamps.public, rust.sell_stamp)
        assert rust.spend(dict(reqs[0], stamp=st))["witness"] == rust.pk
        try:
            rust.spend(dict(reqs[0], stamp=st))
            raise AssertionError("a stamp was redeemed twice")
        except Rejected as e:
            assert "spent stamp" in str(e)
        spare = buy_stamp(rust.stamps.public, rust.sell_stamp)   # bought before the restart
        i0 = idx[0]
        n_before = rust.stamps.public["n"]
        c.kill(i0, signal.SIGKILL)
        c.start(i0)
        c.wait_ready(i0)
        again = RemoteWitness(c.url(i0))
        assert again.stamps.public["n"] == n_before, "the stamp key survives a restart"
        *_, reqs2 = manual_spend(alice, refs, [model.parcel(S, usd, 50, b["lock"], b["salt"])], memo="other")
        try:
            again.spend(dict(reqs2[0], stamp=st))
            raise AssertionError("a redeemed stamp was accepted after a restart")
        except Rejected as e:
            assert "spent stamp" in str(e)
        first = again.status(reqs[0]["sigil"])["votes"]
        assert again.spend(dict(reqs[0], stamp=spare)) == first[0], "a stamp sold before the restart is valid"
        # The wallet's own path: buy a stamp from every witness, then pay.
        net2 = RemoteNetwork({S: [c.url(i) for i in idx]}, timeout=10)
        carol, dave = self.W("carol", net2, S), self.W("dave", net2, S)
        gold = carol.issue("GOLD", 9)
        carol.buy_stamps(S, 2)
        carol.pay(dave, gold, 4)
        dave.buy_stamps(S, 1)
        dave.pay(carol, gold, 1)
        assert (carol.balance(gold), dave.balance(gold)) == (6, 3)

    @check("gossip: proofs, rotations and forks spread through Rust and Python witnesses (gossip_round)")
    def gossip(self):
        from sigil.charter import charter_body, charter_hash, sign_charter
        from sigil.gossip import GossipStore, fork_signers, gossip_round, verify_fork
        from sigil.witnessd import load_key
        c = self.c
        G, idx = self.constellation("gossip", ["rust", "python", "rust", "python"])
        urls = [c.url(i) for i in idx]
        keys = [load_key(c.witnesses[i]["key"]) for i in idx]
        net = RemoteNetwork({G: urls}, timeout=10)
        ws = net.witnesses(G)

        def vote(kp, tid):
            v = {"constellation": G, "version": 0, "witness": kp.pk, "sigil": "11" * 32, "gen": 0, "tid": tid,
                 "time": int(time.time())}
            v["sig"] = kp.sign("vote", model.vote_payload(v))
            return v

        proof = {"a": vote(keys[0], "aa" * 32), "b": vote(keys[0], "bb" * 32)}      # against the Rust G-0
        assert ws[1].gossip({"proofs": [proof]})["proofs"] == 1                     # told to a Python witness
        forged = {"a": proof["a"], "b": dict(proof["b"], sig=proof["a"]["sig"])}
        assert ws[2].gossip({"proofs": [forged, proof["a"], 5]})["proofs"] == 0     # a Rust witness drops junk
        try:
            ws[0].gossip({"proofs": [proof] * 65})
            raise AssertionError("a message over the cap was accepted")
        except Rejected:
            pass
        # A rotation known to one Rust witness, and a conflicting one known to one Python witness.
        cur = net.registry.latest(G)
        v1 = charter_body(cur["name"], 1, [os.urandom(32).hex() for _ in range(4)], charter_hash(cur))
        v1b = charter_body(cur["name"], 1, [os.urandom(32).hex() for _ in range(4)], charter_hash(cur))
        chain0 = net.registry.chain(G)
        a = {"body": v1, "sigs": {k.pk: sign_charter(k, v1) for k in keys[:3]}}
        b = {"body": v1b, "sigs": {k.pk: sign_charter(k, v1b) for k in keys[1:]}}
        assert ws[0].gossip({"charters": {G: chain0 + [a]}})["charters"] == 1
        assert ws[3].gossip({"charters": {G: chain0 + [b]}})["charters"] == 1
        alice = self.W("alice", net, G)
        store = GossipStore(net.registry)
        out = gossip_round(net, store)
        assert out["peers"] == 4 and out["learned"]["proofs"] == 1 and out["learned"]["charters"] == 1
        gossip_round(net, store)
        for w in ws:
            got = w.proofs()
            assert got["proofs"] == [proof], w
            assert len(got["forks"]) == 1 and verify_fork(got["forks"][0]), w
            assert len(w.charters()[G]) == 2, w
        assert fork_signers(store.forks[G]) == {keys[1].pk, keys[2].pk}
        assert store.apply(alice.policy) == 1 and alice.policy.convicted == {keys[0].pk}
        assert gossip_round(net, store)["pushed"] == 0, "a further round is a no-op"

    def run_all(self):
        for t in (self.charters, self.payments, self.swap, self.double_spend, self.release,
                  self.expiry_and_timelocks, self.crash_restart, self.errors, self.rotation,
                  self.regression_reopen, self.regression_sibling, self.stamps, self.gossip):
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
