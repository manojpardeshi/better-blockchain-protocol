"""Store and file-format compatibility across restarts, versions and implementations.

* A witness store written by the current version (Python SQLite, Rust redb) reopens after a
  clean stop (SIGTERM) and after SIGKILL with identical STATUS for every sigil it has seen,
  identical ``/v0/info`` and ``/v0/charters``: bound, released (generation 1), conflicting,
  CONTESTED (``candidates``) and frozen records, before and after a rotation.
* Older formats the code claims to accept still load, from fixtures built as those versions
  wrote them (no older code needed: the formats are rows/keys of canonical JSON):
  Python stores with ``frozen = true`` (before successor binding), records without
  ``candidates`` and ``abstain``, and several rows per ``(kind, key)`` (before the store
  deleted superseded rows); Rust redb stores with ``frozen = true`` and records without
  ``candidates`` (written by ``rust/sigil-witness/tests/legacy_store.rs``, needs cargo).
* Wallet directories saved by the current version reload with the same state and keep
  paying; ``state.json`` without ``trusted``, ``issued``, ``kill_switches`` and the other
  later fields loads with the documented defaults; ``trusted: null`` is refused.
* A constellation rotates from Python witnesses to Rust witnesses (re-using the same key
  files) and back, with payments continuing and old history deep-confirmed: keys and
  registries are interchangeable even though stores are not.
"""

import json
import os
import shutil
import signal
import sqlite3
import subprocess
import time
import unittest

from sigil import Wallet, locks, model, wallet_store
from sigil.charter import Registry, charter_body, charter_hash
from sigil.crypto import KeyPair
from sigil.encoding import canonical
from sigil.server import RemoteNetwork, RemoteWitness
from sigil.store import WitnessStore
from sigil.swap import atomic_swap, propose_swap
from sigil.wallet import SealFailed, request_seal
from sigil.witness import Witness
from sigil.witnessd import load_key, load_registry

from tests.integration.harness import (ROOT, Cluster, Daemon, http, make_tmpdir, manual_spend, new_constellation,
                                       requires_rust, rust_available, store_bytes, write_token)


def sigils_of(wallets, extra=()) -> set:
    out = set(extra)
    for w in wallets:
        for tx in w.dossier.transitions.values():
            out.update(s for s, _ in tx["header"]["inputs"])
        out.update(h["sigil"] for h in w.holdings.values())
    return out


def snapshot(urls: list, sigils: set) -> dict:
    """Everything a witness answers that its store determines."""
    out = {}
    for u in urls:
        info = http(u, "/v0/info")[1]["ok"]
        charters = http(u, "/v0/charters")[1]["ok"]
        st = {s: http(u, "/v0/status", {"sigil": s})[1]["ok"] for s in sorted(sigils)}
        out[info["pk"]] = {"info": info, "charters": charters, "status": st}
    return out


class RestartIdentityMixin:
    KIND = "python"

    def test_restart_identical_status(self):
        kind = self.KIND
        d = make_tmpdir(self, f"restart-{kind}")
        token, tfile = write_token(d)
        c = Cluster(d)
        self.addCleanup(c.stop_all, signal.SIGKILL)
        admin = {kind: ["--admin-token", tfile]}
        X = c.create("home", [kind] * 4, admin)
        c.start_all()
        net = RemoteNetwork(c.directory(), timeout=10)
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd, gold = alice.issue("USD", 1000), bob.issue("GOLD", 50)
        for i in range(6):
            alice.pay(bob, usd, 10 + i)
            bob.pay(alice, gold, 1)
        atomic_swap(alice, usd, 5, bob, gold, 2)
        # A dead swap: mallory seals her input elsewhere, alice releases hers (generation 1).
        mallory = Wallet("mallory", net, X)
        tok = mallory.issue("TOK", 3)
        header, body, _ = propose_swap(alice, usd, 7, mallory, tok, 3)
        unlocks = {**alice.authorise(header, body), **mallory.authorise(header, body)}
        me = mallory.address()
        *_, betrayal = manual_spend(mallory, [body["inputs"][1]], [model.parcel(X, tok, 3, me["lock"], me["salt"])])
        request_seal(net, betrayal[0])
        with self.assertRaises(SealFailed):
            alice.seal(header, body, unlocks)
        self.assertEqual(len(alice.abort(header)), 1)
        alice.pay(bob, usd, 7)
        # A conflicting spend (sealed first), and a split vote that ADOPT turns CONTESTED.
        carol = Wallet("carol", net, X)
        coin, split = carol.issue("C", 5), carol.issue("S", 5)
        refs, _ = carol.select(coin, 5)
        b, a = bob.address(), alice.address()
        *_, r1 = manual_spend(carol, refs, [model.parcel(X, coin, 5, b["lock"], b["salt"])])
        *_, r2 = manual_spend(carol, refs, [model.parcel(X, coin, 5, a["lock"], a["salt"])])
        request_seal(net, r1[0])
        refs2, _ = carol.select(split, 5)
        *_, s1 = manual_spend(carol, refs2, [model.parcel(X, split, 5, b["lock"], b["salt"])])
        *_, s2 = manual_spend(carol, refs2, [model.parcel(X, split, 5, a["lock"], a["salt"])])
        ws = net.witnesses(X)
        for w in ws[:2]:
            w.spend(s1[0])
        for w in ws[2:]:
            w.spend(s2[0])
        extra = {r1[0]["sigil"], s1[0]["sigil"], betrayal[0]["sigil"], "00" * 32}
        # Rotate to four new members of the same kind; old members stay up, frozen.
        old = c.indices(X)
        new_idx = c.add_members(X, [kind] * 4, admin)
        c.start_all(new_idx)
        new_urls = [c.url(i) for i in new_idx]
        self.assertEqual(net.rotate(X, new_urls, token), 1)
        c.write_chain(X, net.registry.chain(X))
        for i in new_idx:
            c.witnesses[i]["pending"] = False
        bob.pay(alice, usd, 3)                                 # under version 1
        contested = RemoteWitness(new_urls[0]).status(s1[0]["sigil"])
        self.assertEqual(contested["tid"], "!contested", contested)
        sigils = sigils_of([alice, bob, carol, mallory], extra)
        urls = [c.url(i) for i in old + new_idx]
        before = snapshot(urls, sigils)
        sizes = {i: store_bytes(c.witnesses[i]["store"]) for i in old + new_idx}
        for sig, label in ((signal.SIGTERM, "SIGTERM"), (signal.SIGKILL, "SIGKILL")):
            for i in old + new_idx:
                c.kill(i, sig)
            if sig == signal.SIGTERM:
                for i in old + new_idx:
                    log = open(c.witnesses[i]["log"]).read()
                    self.assertTrue(log.rstrip().endswith("stopped"), f"{c.witnesses[i]['name']}: {log[-300:]}")
            t = time.monotonic()
            c.start_all(old + new_idx)
            ready = time.monotonic() - t
            after = snapshot(urls, sigils)
            self.assertEqual(after, before, f"{kind}: answers changed after {label} and restart")
            self.assertLess(ready, 20, f"{kind}: restart took {ready:.1f}s")
        for i in old + new_idx:   # reopening must not grow a store (beyond page allocation slack)
            self.assertLessEqual(store_bytes(c.witnesses[i]["store"]), sizes[i] + 1 << 20, c.witnesses[i]["name"])
        # And the restarted network keeps working: payments, the conflict, the frozen side.
        alice.pay(bob, usd, 1)
        with self.assertRaises(SealFailed):
            request_seal(net, r2[0])
        self.assertTrue(all(RemoteWitness(c.url(i))._get("info")["frozen"] for i in old))


class PythonRestartTests(RestartIdentityMixin, unittest.TestCase):
    KIND = "python"


@requires_rust
class RustRestartTests(RestartIdentityMixin, unittest.TestCase):
    KIND = "rust"


# ------------------------------------------------------------------ legacy stores

def legacy_entries(d: str) -> dict:
    """Run a current in-process witness through binds, a conflict and a release; return what a
    store must reproduce: its rows, the requests, and the expected STATUS answers."""
    c = new_constellation(d, "legacy", 4)
    kps = [load_key(k) for k in c["keys"]]
    reg = load_registry(c["registry"])
    cid = c["cid"]
    path = os.path.join(d, "source.db")
    w = Witness(kps[0], reg, lambda: int(time.time()), store=WitnessStore(path))
    w.join(cid, 0)
    owner = KeyPair.from_seed(b"\x05" * 32)
    exp = int(time.time()) + 3600

    def parcel(salt):
        p = model.parcel(cid, "x", 1, locks.sig(owner.pk), salt)
        return p, model.sigil_of(p)

    def req(h, s, p):
        u = locks.empty_unlock(exp)
        u["sigs"][owner.pk] = locks.sign_unlock(owner, s, model.transition_id(h), exp)
        return {"sigil": s, "header": h, "home": cid, "lock": p["lock"], "salt": p["salt"], "unlock": u}

    hdr = lambda inputs, tag: {"inputs": [list(i) for i in inputs], "body": tag * 64}  # noqa: E731
    p1, s1 = parcel("01" * 16)
    pa, sa = parcel("02" * 16)
    px, sx = parcel("03" * 16)
    r1, r2 = req(hdr([(s1, 0)], "1"), s1, p1), req(hdr([(s1, 0)], "2"), s1, p1)
    w.spend(r1)
    swap = hdr([(sa, 0), (sx, 0)], "3")
    w.spend(req(swap, sa, pa))
    ty = hdr([(sx, 0)], "4")
    votes = []
    for k in kps[:3]:
        v = {"constellation": cid, "version": 0, "witness": k.pk, "sigil": sx, "gen": 0,
             "tid": model.transition_id(ty), "time": 1_700_000_000}
        v["sig"] = k.sign("vote", model.vote_payload(v))
        votes.append(v)
    dp = {"kind": "seal", "sigil": sx, "gen": 0, "parcel": {"home": cid, "lock": px["lock"], "salt": px["salt"]},
          "seal": model.seal_from_votes(votes)}
    w.release(sa, dp)
    ra1 = req(hdr([(sa, 1)], "5"), sa, pa)
    w.spend(ra1)
    sigils = [s1, sa, sx, "00" * 32]
    status = {s: w.status(s) for s in sigils}
    rows = list(w.store.db.execute("SELECT kind, key, value FROM log ORDER BY seq"))
    w.store.close()
    return {"c": c, "rows": rows, "status": status, "r1": r1, "r2": r2, "ra1": ra1, "sigils": sigils,
            "vote1": status[s1]["votes"][0], "older_s1": {"gen": 0, "tid": None, "header": None, "vote": None,
                                                         "log": [], "votes": []}}


def write_sqlite(path: str, rows: list) -> None:
    """A store as the reference's log table, rows in the given order (no dedupe)."""
    db = sqlite3.connect(path, isolation_level=None)
    db.execute("CREATE TABLE log (seq INTEGER PRIMARY KEY AUTOINCREMENT, kind TEXT NOT NULL, key TEXT NOT NULL, "
               "value TEXT NOT NULL)")
    db.execute("CREATE INDEX log_kind_key ON log (kind, key)")
    db.executemany("INSERT INTO log (kind, key, value) VALUES (?, ?, ?)", rows)
    db.close()


def write_redb(path: str, rows: list, scratch: str) -> None:
    src = os.path.join(scratch, "raw-entries.json")
    with open(src, "w") as f:
        json.dump([list(r) for r in rows], f)
    cmd = ["cargo", "test", "--release", "--locked", "--manifest-path", os.path.join(ROOT, "rust", "Cargo.toml"),
           "--test", "legacy_store", "--", "--ignored", "--exact", "write_raw_store"]
    out = subprocess.run(cmd, env=dict(os.environ, SIGIL_RAW_ENTRIES=src, SIGIL_RAW_STORE=path),
                         capture_output=True, text=True, timeout=900)
    if out.returncode != 0 or not os.path.exists(path):
        raise RuntimeError(out.stdout[-2000:] + out.stderr[-2000:])


def strip_record(value: str, fields: tuple) -> str:
    rec = json.loads(value)
    for f in fields:
        rec.pop(f, None)
    return canonical(rec).decode()


class LegacyStoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.d = make_tmpdir(cls, "legacy")
        cls.L = legacy_entries(cls.d)
        cls.token, cls.tfile = write_token(cls.d)
        os.makedirs(os.path.join(cls.d, "logs"), exist_ok=True)

    def rows(self, *, drop=(), frozen=False, duplicates=False) -> list:
        out = []
        for kind, key, value in self.L["rows"]:
            if kind == "record":
                value = strip_record(value, drop)
            out.append((kind, key, value))
        if duplicates:  # an older value of each row first, as the store kept before it deleted them
            s1 = self.L["sigils"][0]
            older = [("member", "", canonical([self.L["c"]["cid"], 0]).decode()),
                     ("record", s1, canonical(self.L["older_s1"]).decode())]
            out = older + out
        if frozen:
            out.append(("frozen", "", "true"))
        return out

    def daemon(self, kind: str, store: str) -> Daemon:
        c = self.L["c"]
        dmn = Daemon(kind, c["keys"][0], c["registry"], c["cid"], store,
                     os.path.join(self.d, "logs", os.path.basename(store) + ".log"), args=["--admin-token", self.tfile])
        dmn.start()
        self.addCleanup(dmn.stop)
        return dmn

    def check(self, dmn: Daemon, frozen: bool):
        L = self.L
        for s in L["sigils"]:
            self.assertEqual(http(dmn.url, "/v0/status", {"sigil": s})[1]["ok"], L["status"][s], (dmn.kind, s))
        info = http(dmn.url, "/v0/info")[1]["ok"]
        self.assertEqual((info["constellation"], info["version"], info["frozen"]), (L["c"]["cid"], 0, frozen))
        tok = {"Authorization": f"Bearer {self.token}"}
        if frozen:
            self.assertEqual(http(dmn.url, "/v0/spend", {"request": L["r1"]})[:2],
                             (403, {"error": "rejected", "message": "witness not active", "vote": None}))
            # The successor of a `true` store is unknown: every FREEZE is refused, even a valid one.
            cur = json.load(open(L["c"]["registry"]))[L["c"]["cid"]][0]["body"]
            nxt = charter_body(cur["name"], 1, cur["witnesses"], charter_hash(cur))
            self.assertEqual(http(dmn.url, "/v0/freeze", {"charter": nxt}, headers=tok)[:2],
                             (403, {"error": "rejected", "message": "already frozen for a different successor charter",
                                    "vote": None}))
            self.assertEqual(http(dmn.url, "/v0/heartbeat", {"challenge": "x"})[0], 403)
        else:
            self.assertEqual(http(dmn.url, "/v0/spend", {"request": L["r1"]})[1]["ok"], L["vote1"])
            code, body, _ = http(dmn.url, "/v0/spend", {"request": L["r2"]})
            self.assertEqual((code, body["error"], body["vote"]), (409, "conflict", L["vote1"]))
            code, body, _ = http(dmn.url, "/v0/spend", {"request": L["ra1"]})
            self.assertEqual((code, body["ok"]["gen"]), (200, 1))

    def test_python_store_without_candidates_and_abstain_with_duplicate_rows(self):
        p = os.path.join(self.d, "py-old.db")
        write_sqlite(p, self.rows(drop=("candidates", "abstain"), duplicates=True))
        dmn = self.daemon("python", p)
        self.check(dmn, frozen=False)
        # Restarted after writing to it, it still reads the last row of each (kind, key).
        dmn.stop()
        dmn.start()
        for s in self.L["sigils"][:1]:
            self.assertEqual(http(dmn.url, "/v0/status", {"sigil": s})[1]["ok"], self.L["status"][s])

    def test_python_store_frozen_true(self):
        p = os.path.join(self.d, "py-frozen.db")
        write_sqlite(p, self.rows(drop=("candidates", "abstain"), frozen=True))
        self.check(self.daemon("python", p), frozen=True)

    @requires_rust
    def test_rust_store_without_candidates(self):
        if shutil.which("cargo") is None:
            self.skipTest("cargo not available to write the redb fixture")
        p = os.path.join(self.d, "rs-old.redb")
        write_redb(p, self.rows(drop=("candidates",)), self.d)
        self.check(self.daemon("rust", p), frozen=False)

    @requires_rust
    def test_rust_store_frozen_true(self):
        if shutil.which("cargo") is None:
            self.skipTest("cargo not available to write the redb fixture")
        p = os.path.join(self.d, "rs-frozen.redb")
        write_redb(p, self.rows(drop=("candidates",), frozen=True), self.d)
        self.check(self.daemon("rust", p), frozen=True)

    def test_current_python_store_rows_are_what_rust_writes(self):
        """The two stores hold the same (kind, key, value) facts: a Rust store built from the
        Python rows answers like the Python witness (checked above); here, the Python rows
        have exactly the kinds store.py documents."""
        kinds = {k for k, _, _ in self.L["rows"]}
        self.assertLessEqual(kinds, {"pk", "member", "frozen", "record", "stamp"})


# ------------------------------------------------------------------ wallets

class WalletDirTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = cls.d = make_tmpdir(cls, "wallets")
        c = cls.c = Cluster(d)
        cls.addClassCleanup(c.stop_all, signal.SIGKILL)
        cls.X = c.create("orion", ["python"] * 4)
        cls.Y = c.create("lyra", ["python"] * 4)
        c.start_all()

    def net(self):
        return RemoteNetwork(self.c.directory(), timeout=10)

    @staticmethod
    def state(w: Wallet) -> dict:
        return {"holdings": w.holdings, "pledged": w.pledged, "pending": w.pending, "issued": w.issued,
                "kill": w.kill_switches, "trusted": w.policy.trusted, "convicted": w.policy.convicted,
                "stamps": dict(w.stamps), "confirmed": w._confirmed, "keys": set(w.keys), "seeds": w.seeds,
                "dossier": w.dossier.to_json(), "home": w.home, "deep": w.deep_threshold,
                "ttl": w.pledge_ttl, "skew": w.max_skew}

    def test_current_wallet_reloads_and_keeps_paying(self):
        net = self.net()
        alice, bob = Wallet("alice", net, self.X, deep_threshold=50), Wallet("bob", net, self.Y)
        usd, gold = alice.issue("USD", 1000), bob.issue("GOLD", 10)
        alice.pay(bob, usd, 100)
        atomic_swap(alice, usd, 10, bob, gold, 1)            # kill switches
        unused = alice.address()                              # issued, not yet paid
        refs, _ = alice.select(usd, 5)                        # a pledge left pending
        b = bob.address()
        hd, bd, _ = alice.prepare(refs, [model.parcel(self.Y, usd, 5, b["lock"], b["salt"])])
        alice.authorise(hd, bd)
        d = os.path.join(self.d, "alice")
        wallet_store.save(alice, d)
        self.assertEqual(oct(os.stat(os.path.join(d, "keys.json")).st_mode & 0o777), "0o600")
        again = wallet_store.load(d, self.net())
        self.assertEqual(self.state(again), self.state(alice))
        bob.pay(again, usd, 20)                               # receives after reload
        to = Wallet("carol", bob.network, self.X)
        bob.network.refresh_charters(self.X)
        # pay to the address issued before the save
        r2, outs = bob.payment_outputs(usd, 1, unused)
        tid = bob.transact(r2, outs)
        again.receive(bob.dossier.ancestry([tid]), [model.ref(tid, 0)])
        again.pay(to, usd, 15)                                # from what is not pledged
        self.assertEqual(again.balance(usd), 1000 - 100 - 10 + 20 + 1 - 15)
        wallet_store.save(again, d)
        self.assertEqual(self.state(wallet_store.load(d, self.net())), self.state(again))

    def legacy_dir(self, name: str, drop: tuple, two_tuple_pledges: bool = False):
        net = self.net()
        w, peer = Wallet(name, net, self.X), Wallet(name + "-peer", net, self.X)
        usd = w.issue("USD", 100)
        w.pay(peer, usd, 10)
        refs, _ = w.select(usd, 5)
        a = peer.address()
        hd, bd, _ = w.prepare(refs, [model.parcel(self.X, usd, 5, a["lock"], a["salt"])])
        w.authorise(hd, bd)
        d = os.path.join(self.d, name)
        wallet_store.save(w, d)
        p = os.path.join(d, "state.json")
        st = json.load(open(p))
        for k in drop:
            st.pop(k, None)
        if two_tuple_pledges:
            st["pledged"] = {s: v[:2] for s, v in st["pledged"].items()}
        with open(p, "w") as f:
            json.dump(st, f)
        return w, peer, usd, d

    def test_legacy_wallet_without_later_fields_loads(self):
        drop = ("version", "trusted", "issued", "kill_switches", "pledge_ttl", "max_skew", "deep_after_succession",
                "pending", "completed", "convicted")
        w, peer, usd, d = self.legacy_dir("legacy", drop, two_tuple_pledges=True)
        old = wallet_store.load(d, self.net())
        self.assertEqual((old.pledge_ttl, old.max_skew, old.deep_after_succession), (600, 120, True))
        self.assertEqual(old.policy.trusted, {self.X, self.Y})   # the default, never "any"
        self.assertEqual(old.issued, {h["sigil"] for h in w.holdings.values()})
        self.assertEqual(old.kill_switches, set())
        self.assertTrue(all(len(v) == 3 and v[2] == 0 for v in old.pledged.values()), old.pledged)
        self.assertEqual(old.balance(usd), w.balance(usd))
        # It keeps working: receives at a fresh address and pays from unpledged funds.
        peer.pay(old, usd, 3)
        old.pay(peer, usd, 2)
        self.assertEqual(old.balance(usd), w.balance(usd) + 3 - 2)

    def test_trusted_null_is_refused(self):
        _, _, _, d = self.legacy_dir("nulltrust", ())
        p = os.path.join(d, "state.json")
        st = json.load(open(p))
        st["trusted"] = None
        with open(p, "w") as f:
            json.dump(st, f)
        with self.assertRaises(ValueError):
            wallet_store.load(d, self.net())


# ------------------------------------------------------------------ rotation across implementations

@requires_rust
class CrossImplementationRotationTests(unittest.TestCase):
    def test_python_to_rust_and_back_with_the_same_keys(self):
        d = make_tmpdir(self, "xrot")
        token, tfile = write_token(d)
        c = Cluster(d)
        self.addCleanup(c.stop_all, signal.SIGKILL)
        admin = {"rust": ["--admin-token", tfile], "python": ["--admin-token", tfile]}
        X = c.create("relay", ["python"] * 4, admin)
        c.start_all()
        keys = [c.witnesses[i]["key"] for i in c.indices(X)]
        net = RemoteNetwork(c.directory(), timeout=10)
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd = alice.issue("USD", 500)
        alice.pay(bob, usd, 50)
        # A binding no payment completes: every later version must inherit it.
        coin = alice.issue("C", 1)
        refs, _ = alice.select(coin, 1)
        b, a = bob.address(), alice.address()
        *_, r1 = manual_spend(alice, refs, [model.parcel(X, coin, 1, b["lock"], b["salt"])])
        *_, r2 = manual_spend(alice, refs, [model.parcel(X, coin, 1, a["lock"], a["salt"])])
        request_seal(net, r1[0])
        steps = [["rust"] * 4, ["python"] * 4, ["rust", "python", "rust", "python"]]
        frozen_by_kind = {}
        for v, kinds in enumerate(steps, start=1):
            old = c.indices(X)
            new = c.add_members(X, kinds, admin, keys=keys if v < 3 else None)
            c.start_all(new)
            urls = [c.url(i) for i in new]
            self.assertEqual(net.rotate(X, urls, token), v)
            c.write_chain(X, net.registry.chain(X))
            for i in new:
                c.witnesses[i]["pending"] = False
            for i in old:
                frozen_by_kind.setdefault(c.witnesses[i]["kind"], c.url(i))
            self.assertEqual({w.version for w in net.witnesses(X)}, {v})
            # Payments continue, and the inherited binding still refuses the conflicting spend.
            bob.pay(alice, usd, 5)
            alice.pay(bob, usd, 7)
            with self.assertRaises(SealFailed):
                request_seal(net, r2[0])
            for w in net.witnesses(X):
                self.assertEqual(w.spend(r1[0])["tid"], model.transition_id(r1[0]["header"]))
            # Stop the frozen predecessors except one of each kind, to check they stay frozen.
            for i in old:
                if c.url(i) not in frozen_by_kind.values():
                    c.kill(i, signal.SIGTERM)
        # A fresh holder deep-confirms history sealed by versions 0..3 (Python, Rust, Python, mixed).
        erin = Wallet("erin", RemoteNetwork({X: net.urls[X]}, timeout=10), X, deep_threshold=1)
        bob.pay(erin, usd, 4)
        self.assertEqual(erin.balance(usd), 4)
        self.assertGreaterEqual(len(erin._confirmed), 2)
        for kind, url in frozen_by_kind.items():
            info = http(url, "/v0/info")[1]["ok"]
            self.assertTrue(info["frozen"], kind)
            self.assertEqual(http(url, "/v0/spend", {"request": r1[0]})[0], 403, kind)


if __name__ == "__main__":
    unittest.main()
