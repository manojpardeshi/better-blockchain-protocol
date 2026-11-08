"""One seeded chaos run: a multi-process constellation, wallets at work, faults everywhere.

    python -m tests.integration.chaos.run --seeds 1-20 [--ops 60] [--minutes 60] [--out stats.json]

A run (``ChaosRun``):

1. **Setup.** 2-3 constellations of 4, 5 or 7 witness processes, Rust and Python mixed
   (``Config.random`` draws the shape from the seed); constellation 0 may have a successor
   committee of 4 mixed standby members probing it for heartbeats; Byzantine processes
   within (or, for non-vacuity, beyond) *f*; every process behind a ``FaultProxy``.
   Honest wallets (alice, bob, carol, dave) issue assets; mallory is an equivocating owner.
2. **Workload with faults.** Worker threads pay, swap, settle expired pledges, let mallory
   try double spends, run the delayed-request/expiry scenario, and the operator rotates a
   constellation and, after cutting the committee off from the home for longer than
   ``dead_man``, drives a succession. Meanwhile a chaos thread SIGKILLs and restarts
   processes (also from proxy hooks at chosen points: mid-SPEND, mid-RELEASE, mid-MIRROR,
   mid-FREEZE/ADOPT, mid-STANDBY/SUCCEED, mid-commit), drops / delays / duplicates /
   reorders / holds requests, partitions witnesses and standby members, skews clocks and
   fills disks.
3. **Heal and settle.** Every fault is cleared, every process restarted, held requests are
   delivered late, and each wallet must settle its pledges and make a fresh payment within
   ``liveness_bound`` seconds.
4. **Check.** ``invariants.check`` (S1, S1b, S2, S5, S6) on everything observed plus a final
   STATUS sweep of every honest process; S3 (supply conserved per asset, nothing credited
   twice, nothing held that a complete transition consumed) and S4 (every holding verifies
   with a fresh verifier) on the wallets.

``ChaosRun.result`` holds the statistics: operations by kind and outcome, faults injected,
violations, liveness failures and anomalies (unexpected exception types inside wallet code).
"""

import argparse
import json
import os
import random
import shutil
import signal
import sys
import tempfile
import threading
import time
import traceback
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field

from sigil import Wallet, locks, model
from sigil.charter import Registry, faults, quorum
from sigil.server import RemoteNetwork, RemoteStandby, RemoteWitness, RotationIncomplete
from sigil.swap import _pays, propose_swap
from sigil.validate import InvalidDossier, TrustPolicy, Verifier
from sigil.wallet import SealFailed, mirror_acks
from sigil.witness import Conflict, Rejected

from . import invariants
from .cluster import RUST_BIN, TOKEN, ChaosCluster, build_skew_shim, tmpfs_available

EXPECTED = (SealFailed, ValueError, InvalidDossier, Rejected, RotationIncomplete, RuntimeError)


def rust_available() -> bool:
    return os.path.exists(RUST_BIN) and os.access(RUST_BIN, os.X_OK)


@dataclass
class Config:
    seed: int
    ops: int = 40
    workers: int = 2
    sizes: list = field(default_factory=lambda: [4, 4])   # witnesses per constellation
    kinds: str = "mixed"            # mixed | rust | python
    byz: int = 0                    # Byzantine witnesses in constellation 0
    byz_modes: str = "equivocate,lie,withhold,garbage"
    byz_other: int = 0              # Byzantine witnesses in each other constellation (<= f)
    committee: bool = True          # constellation 0 has a successor committee
    dead_man: int = 4
    probe_every: float = 0.5
    rotation: bool = True
    succession: bool = True
    kills: bool = True
    hooks: bool = True
    net_faults: bool = True
    partitions: bool = True
    skew: str = "within"            # none | within | beyond_f | beyond_q
    disk: bool = True
    mutant: str | None = None       # every honest witness of constellation 0 runs this mutant
    mallory: bool = True
    mallory_targeted: float = 0.5
    delayed_expiry: int = 1         # how many delayed-request scenarios
    pledge_ttl: int = 4
    max_skew: int = 3
    client_timeout: float = 1.5
    liveness_bound: float = 150.0
    deep_threshold: int = 200
    chaos_rate: float = 1.0         # scales how often the chaos thread acts

    @classmethod
    def random(cls, seed: int, **over) -> "Config":
        r = random.Random(seed)
        n_const = r.choice([2, 2, 3])
        sizes = [r.choice([4, 4, 5, 7]) for _ in range(n_const)]
        cfg = cls(seed=seed, sizes=sizes, kinds=r.choice(["mixed", "mixed", "mixed", "rust", "python"]),
                  committee=r.random() < 0.7, rotation=r.random() < 0.6, succession=r.random() < 0.5,
                  skew=r.choice(["none", "within", "within", "beyond_f"]),
                  byz=r.choice([0, 0, 1]), byz_other=r.choice([0, 0, 1]),
                  disk=r.random() < 0.5, delayed_expiry=r.choice([0, 1, 1, 2]),
                  workers=r.choice([1, 2, 2, 3]))
        cfg.succession = cfg.succession and cfg.committee
        for k, v in over.items():
            setattr(cfg, k, v)
        if cfg.byz > faults(cfg.sizes[0]) and "beyond" not in str(over.get("note", "")):
            pass  # beyond-f runs are allowed (non-vacuity); the result says so
        return cfg


class Anomaly(Exception):
    pass


class ChaosRun:
    def __init__(self, cfg: Config, workdir: str | None = None, keep: bool = False, log=None):
        self.cfg = cfg
        self.rng = random.Random(cfg.seed)
        self.keep = keep
        self.tmp = workdir or tempfile.mkdtemp(prefix=f"sigil-chaos-{cfg.seed}-")
        self.log_fn = log
        self.obs = invariants.Observer()
        self.skew_so = build_skew_shim(self.tmp) if cfg.skew != "none" else None
        self.c = ChaosCluster(os.path.join(self.tmp, "cluster"), self.obs, cfg.seed, skew_so=self.skew_so,
                              client_timeout=cfg.client_timeout + 0.5)
        self.stop = threading.Event()
        self.ops = Counter()
        self.faults = Counter()
        self.anomalies: list = []
        self.violations: list = []
        self.liveness: list = []
        self.notes: list = []
        self.released: list = []          # (sigil, gen, tid) pledges honest wallets released
        self.payee_of: dict = {}          # tid -> (payer, payee, [ref])
        self.undelivered: list = []       # (payer, payee, tid, refs)
        self.swaps: list = []             # (a, b, header, body, tid)
        self.wallet_locks: dict = {}
        self.op_lock = threading.Lock()   # operator: one rotation/succession at a time
        self.dir_lock = threading.Lock()
        self.directory: dict = {}
        self.committees: dict = {}
        self.cids: list = []
        self.byz_idx: set = set()
        self.faulty_clock: set = set()    # witness indices whose clock left the bound
        self.restart_timers: list = []
        self.started = time.monotonic()
        self.result: dict = {}

    # ------------------------------------------------------------ logging

    def log(self, msg: str) -> None:
        line = f"[seed {self.cfg.seed} {time.monotonic() - self.started:7.1f}s] {msg}"
        self.notes.append(line)
        if self.log_fn:
            self.log_fn(line)

    def anomaly(self, where: str, exc: BaseException) -> None:
        tb = traceback.extract_tb(exc.__traceback__)
        frames = [f for f in tb if "/sigil/" in f.filename] or tb
        loc = f"{os.path.relpath(frames[-1].filename)}:{frames[-1].lineno} in {frames[-1].name}" if frames else "?"
        key = f"{type(exc).__name__} at {loc}"
        self.anomalies.append({"op": where, "key": key, "error": repr(exc)[:300],
                               "trace": "".join(traceback.format_exception(exc))[-2500:]})
        self.log(f"ANOMALY in {where}: {key}: {exc!r}"[:300])

    # ------------------------------------------------------------ setup

    def _kinds(self, n: int) -> list:
        if self.cfg.kinds == "rust":
            return ["rust"] * n
        if self.cfg.kinds == "python":
            return ["python"] * n
        ks = [self.rng.choice(["rust", "python"]) for _ in range(n)]
        ks[0], ks[-1] = "rust", "python"
        return ks

    def setup(self) -> None:
        cfg, c = self.cfg, self.c
        names = ["orion", "lyra", "vega"]
        for ci, n in enumerate(cfg.sizes):
            kinds = self._kinds(n)
            nbyz = cfg.byz if ci == 0 else min(cfg.byz_other, faults(n))
            for j in range(nbyz):
                kinds[1 + j] = "byz:" + cfg.byz_modes
            if ci == 0 and cfg.mutant:
                kinds = [("mutant:" + cfg.mutant) if k == "python" or k == "rust" else k for k in kinds]
            committee = self._kinds(4) if (ci == 0 and cfg.committee) else None
            cid = c.create(names[ci], kinds, committee=committee, dead_man=cfg.dead_man if committee else None)
            self.cids.append(cid)
            for i in c.indices(cid):
                if c.witnesses[i]["kind"].startswith("byz:"):
                    self.byz_idx.add(i)
            if committee:
                members = [c.probe_url(i) for i in c.indices(cid)]
                for i in c.indices(cid, role="standby"):
                    c.witnesses[i]["args"] += ["--members", *members, "--probe-every", str(cfg.probe_every)]
        if cfg.disk and tmpfs_available(os.path.join(self.tmp, "probe-mnt")):
            for i in self._honest_witnesses():
                if self.rng.random() < 0.3:
                    if c.put_on_tmpfs(i, 2048):
                        self.faults["tmpfs-store"] += 1
        for i in range(len(c.witnesses)):
            self._register_pk(i)
        c.start_all()
        for cid in self.cids:
            self.directory[cid] = [c.url(i) for i in c.indices(cid)]
            ks = c.indices(cid, role="standby")
            if ks:
                self.committees[cid] = [c.url(i) for i in ks]
        self._initial_skews()
        homes = [self.cids[0], self.cids[1], self.cids[-1], self.cids[1 % len(self.cids)]]
        self.wallets = {}
        for name, home in zip(["alice", "bob", "carol", "dave"], homes):
            self.wallets[name] = self._wallet(name, home)
        self.mallory = self._wallet("mallory", self.cids[0], honest=False)
        self.assets: dict = {}  # asset id -> supply (honest assets only)
        for name, w in self.wallets.items():
            a = w.issue(name.upper(), 1000)
            self.assets[a] = 1000
        self.mal_asset = self.mallory.issue("MAL", 64)
        self.mal_coins = 8
        # split mallory's coin into small parcels to double-spend later (no faults yet)
        self._split_mallory()
        self.log(f"setup: sizes={cfg.sizes} kinds={[w['kind'] for w in c.witnesses]} "
                 f"committee={bool(self.committees)} byz={len(self.byz_idx)}")

    def _register_pk(self, i: int) -> None:
        w = self.c.witnesses[i]
        with open(w["key"]) as f:
            pk = json.load(f)["pk"]
        w["pk"] = pk
        self.c._ensure_proxies(i)
        self.obs.pk_of[self.c.proxies[i].name] = pk
        if i in self.c.probes:
            self.obs.pk_of[self.c.probes[i].name] = pk

    def _honest_witnesses(self, cid=None) -> list:
        return [i for i, w in enumerate(self.c.witnesses)
                if w.get("role") != "standby" and i not in self.byz_idx and (cid is None or w["cid"] == cid)]

    def _wallet(self, name: str, home: str, honest: bool = True) -> Wallet:
        net = RemoteNetwork(dict(self.directory), committees=dict(self.committees), timeout=self.cfg.client_timeout)
        w = Wallet(name, net, home, pledge_ttl=self.cfg.pledge_ttl, max_skew=self.cfg.max_skew,
                   deep_threshold=self.cfg.deep_threshold if honest else None)
        self.wallet_locks[name] = threading.Lock()
        if honest:
            real = w.unpledge_if_unbound

            def unpledge(sigil, _real=real, _w=w):
                pledge = _w.pledged.get(sigil)
                ok = _real(sigil)
                if ok and pledge is not None:
                    self.released.append((sigil, pledge[0], pledge[1]))
                    self.faults["pledges-released"] += 1
                    hook = getattr(_w, "_chaos_on_release", None)
                    if hook is not None:
                        hook(sigil)
                return ok

            w.unpledge_if_unbound = unpledge
        return w

    def _split_mallory(self) -> None:
        m = self.mallory
        outs = []
        for _ in range(self.mal_coins):
            a = m.address()
            outs.append(model.parcel(a["home"], self.mal_asset, 64 // self.mal_coins, a["lock"], a["salt"]))
        refs, _ = m.select(self.mal_asset, 64)
        for attempt in range(5):
            try:
                m.transact(refs, outs)
                return
            except SealFailed as e:
                self.log(f"mallory split failed: {e}")
                time.sleep(1)
        self.notes.append("mallory split never sealed")

    def _initial_skews(self) -> None:
        cfg, c = self.cfg, self.c
        if self.skew_so is None:
            return
        for i in self._honest_witnesses():
            if cfg.skew in ("within", "beyond_f", "beyond_q"):
                c.set_skew(i, self.rng.randint(-(cfg.max_skew - 1), cfg.pledge_ttl // 2))
        if cfg.skew == "beyond_f":
            for cid in self.cids:
                budget = faults(len(self.c.indices(cid))) - len([i for i in self.byz_idx if c.witnesses[i]["cid"] == cid])
                for i in self.rng.sample(self._honest_witnesses(cid), max(0, budget)):
                    c.set_skew(i, -self.rng.randint(cfg.max_skew + 2, 4 * cfg.max_skew))
                    self.faulty_clock.add(i)
        if cfg.skew == "beyond_q":
            for i in self._honest_witnesses(self.cids[0]):
                c.set_skew(i, -(cfg.pledge_ttl + 4 * cfg.max_skew + 6))
                self.faulty_clock.add(i)

    # ------------------------------------------------------------ helpers

    def _locked(self, *names):
        class _L:
            def __init__(s, locks_):
                s.locks = locks_

            def __enter__(s):
                for lk in s.locks:
                    lk.acquire()

            def __exit__(s, *a):
                for lk in reversed(s.locks):
                    lk.release()
        return _L([self.wallet_locks[n] for n in sorted(set(names))])

    def _holding_asset(self, w: Wallet):
        assets = Counter()
        for h in w.holdings.values():
            p = h["parcel"]
            if p["lock"]["op"] == "sig" and h["sigil"] not in w.pledged and p["asset"] in self.assets:
                assets[p["asset"]] += p["amount"]
        return assets

    def _deliver(self, payer: Wallet, payee: Wallet, tid: str, refs: list) -> bool:
        try:
            payee.receive(payer.dossier.ancestry([tid]), refs)
            return True
        except InvalidDossier as e:
            if "already used" in str(e):
                return True
            self.undelivered.append((payer.name, payee.name, tid, refs))
            self.ops["receive-deferred"] += 1
            return False
        except Rejected:
            self.undelivered.append((payer.name, payee.name, tid, refs))
            self.ops["receive-deferred"] += 1
            return False

    def _transact(self, payer: Wallet, refs: list, outputs: list, payee: Wallet | None):
        header, body, tid = payer.prepare(refs, outputs)
        if payee is not None:
            self.payee_of[tid] = (payer.name, payee.name, [model.ref(tid, 0)])
        unlocks = payer.authorise(header, body)
        try:
            payer.seal(header, body, unlocks)
        except SealFailed:
            for s, _g in header["inputs"]:
                payer.unpledge_if_unbound(s)
            raise
        payer.finalise(header, body, unlocks)
        return tid

    # ------------------------------------------------------------ operations

    def op_pay(self, r: random.Random) -> str:
        names = list(self.wallets)
        a, b = r.sample(names, 2)
        payer, payee = self.wallets[a], self.wallets[b]
        with self._locked(a, b):
            payer.release_expired_pledges()
            self._deliver_completed(payer)
            assets = self._holding_asset(payer)
            if not assets:
                return "no-funds"
            asset = r.choice(sorted(assets))
            amount = r.randint(1, max(1, min(assets[asset], 60)))
            home = r.choice(self.cids + [payee.home] * 2)
            addr = payee.address(home)
            refs, outputs = payer.payment_outputs(asset, amount, addr)
            tid = self._transact(payer, refs, outputs, payee)
            self._deliver(payer, payee, tid, [model.ref(tid, 0)])
            return "ok"

    def op_swap(self, r: random.Random) -> str:
        names = [n for n in self.wallets]
        a_name, b_name = r.sample(names, 2)
        a, b = self.wallets[a_name], self.wallets[b_name]
        with self._locked(a_name, b_name):
            for w in (a, b):
                w.release_expired_pledges()
                self._deliver_completed(w)
            aa, ba = self._holding_asset(a), self._holding_asset(b)
            if not aa or not ba:
                return "no-funds"
            x, y = r.choice(sorted(aa)), r.choice(sorted(ba))
            ax, by = r.randint(1, min(aa[x], 30)), r.randint(1, min(ba[y], 30))
            header, body, terms = propose_swap(a, x, ax, b, y, by)
            tid = model.transition_id(header)
            self.swaps.append((a_name, b_name, header, body, tid))
            for party, key in ((a, "a"), (b, "b")):
                if not _pays(body, *terms[key]):
                    raise Anomaly("swap does not pay")
            unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
            kills = (a.kill_switches | b.kill_switches) & {s for s, _ in header["inputs"]}
            a.seal(header, body, unlocks, only={s for s, _ in header["inputs"]} - kills)
            unlocks.update({**a.authorise(header, body, release_kill=True),
                            **b.authorise(header, body, release_kill=True)})
            a.seal(header, body, unlocks, only=kills)
            self._finish_swap(a, b, header, body, unlocks)
            return "ok"

    def _finish_swap(self, a: Wallet, b: Wallet, header, body, unlocks) -> None:
        tid = model.transition_id(header)
        b.dossier.merge(a.dossier.ancestry({r["tx"] for r in body["inputs"]}))
        for seal in a.dossier.seals.values():
            if seal["tid"] == tid:
                b.dossier.add_seal(seal)
        for party in (a, b):
            party.finalise(header, body, unlocks)
            party.verifier.verify_transition(party.dossier, tid)

    def op_settle(self, r: random.Random) -> str:
        name = r.choice(list(self.wallets))
        w = self.wallets[name]
        with self._locked(name):
            freed = w.release_expired_pledges()
            self._deliver_completed(w)
            return "freed" if freed else "nothing"

    def _deliver_completed(self, payer: Wallet) -> None:
        """Transitions a retry completed (``Wallet.completed``) go to their payees at settle time."""
        while payer.completed:
            tid = payer.completed.pop()
            if tid in self.payee_of:
                _, pname, refs = self.payee_of[tid]
                self.undelivered.append((payer.name, pname, tid, refs))

    def op_mallory(self, r: random.Random) -> str:
        m = self.mallory
        with self._locked("mallory"):
            coins = [h for h in m.holdings.values() if h["parcel"]["asset"] == self.mal_asset]
            if not coins:
                return "no-coins"
            h = r.choice(coins)
            net = m.network
            reqs, hdrs = [], []
            for k in range(2):
                a = m.address()
                out = [model.parcel(a["home"], self.mal_asset, h["parcel"]["amount"], a["lock"], a["salt"])]
                header, body, tid = m.prepare([h["ref"]], out, memo=f"mallory-{k}-{r.random()}")
                exp = int(time.time()) + self.cfg.pledge_ttl
                u = locks.empty_unlock(exp)
                for pk in locks.keys_in(h["parcel"]["lock"]) & set(m.keys):
                    u["sigs"][pk] = locks.sign_unlock(m.keys[pk], h["sigil"], tid, exp)
                p = h["parcel"]
                req = {"sigil": h["sigil"], "header": header, "home": p["home"], "lock": p["lock"],
                       "salt": p["salt"], "unlock": u}
                acks = mirror_acks(net, req)
                if acks:
                    req = dict(req, mirror=acks)
                reqs.append(req)
                hdrs.append((header, body, {h["sigil"]: u}, tid))
            ws = net.witnesses(h["parcel"]["home"])
            byz_pks = {self.c.witnesses[i]["pk"] for i in self.byz_idx}
            if r.random() < self.cfg.mallory_targeted:
                honest = [w for w in ws if w.pk not in byz_pks]
                r.shuffle(honest)
                half = len(honest) // 2
                plan = [(w, 0) for w in honest[:half]] + [(w, 1) for w in honest[half:]]
                plan += [(w, k) for w in ws if w.pk in byz_pks for k in (0, 1)]
            else:
                plan = [(w, r.randrange(2)) for w in ws] + [(r.choice(ws), r.randrange(2)) for _ in range(2)]
            r.shuffle(plan)
            votes = defaultdict(dict)

            def go(item):
                w, k = item
                try:
                    v = w.spend(reqs[k])
                except Rejected:
                    return
                if isinstance(v, dict) and v.get("tid") == hdrs[k][3]:
                    votes[k][v.get("witness")] = v

            with ThreadPoolExecutor(4) as ex:
                list(ex.map(go, plan))
            sealed = []
            for k in (0, 1):
                vs = list(votes[k].values())
                if vs:
                    seal = model.seal_from_votes(vs)
                    from sigil.proofs import verify_seal
                    if verify_seal(seal, net.registry):
                        sealed.append((k, seal))
            if len(sealed) == 2:
                self.log("mallory sealed BOTH transitions")
            for k, seal in sealed[:1]:
                header, body, unlocks, tid = hdrs[k]
                m.dossier.add_seal(seal)
                m.finalise(header, body, unlocks)
            if not sealed:
                m.holdings.pop(model.parcel_id(h["ref"]), None)
            return f"sealed-{len(sealed)}"

    def op_delayed_expiry(self, r: random.Random) -> str:
        """SPEC §4 rule 3: the spend is held in flight past expiry, then delivered late."""
        names = [n for n in self.wallets]
        a, b, c2 = (r.sample(names, 3) + names)[:3]
        payer, p1, p2 = self.wallets[a], self.wallets[b], self.wallets[c2]
        with self._locked(a, b, c2):
            payer.release_expired_pledges()
            assets = self._holding_asset(payer)
            if not assets:
                return "no-funds"
            asset = r.choice(sorted(assets))
            amount = r.randint(1, min(assets[asset], 20))
            refs, outputs = payer.payment_outputs(asset, amount, p1.address())
            sigils = {payer.holdings[model.parcel_id(x)]["sigil"] for x in refs}
            homes = {payer.holdings[model.parcel_id(x)]["parcel"]["home"] for x in refs}
            proxies = [self.c.proxies[i] for i in range(len(self.c.witnesses))
                       if self.c.witnesses[i]["cid"] in homes and self.c.witnesses[i].get("role") != "standby"]

            def mine(method, body_bytes, _s=sigils):
                try:
                    return method == "spend" and json.loads(body_bytes)["request"]["sigil"] in _s
                except (ValueError, KeyError, TypeError):
                    return False

            for p in proxies:
                p.hold_filter = mine
            try:
                try:
                    self._transact(payer, refs, outputs, p1)
                    return "not-held"   # e.g. the home rotated away from these proxies meanwhile
                except SealFailed:
                    pass
            finally:
                for p in proxies:
                    p.hold_filter = None
            held = sum(len(p.held) for p in proxies)
            self.faults["held-for-expiry"] += held

            def on_release(sigil, _p=proxies, _s=sigils):
                if sigil in _s:
                    n = sum(p.deliver_held(lambda m_, b_: mine(m_, b_)) for p in _p)
                    self.faults["delivered-after-expiry"] += n

            payer._chaos_on_release = on_release
            try:
                time.sleep(self.cfg.pledge_ttl + self.cfg.max_skew + 1.5)
                assets = self._holding_asset(payer)
                payer.release_expired_pledges()
                assets = self._holding_asset(payer)
                if asset not in assets:
                    return "still-pledged"
                refs2, outputs2 = payer.payment_outputs(asset, min(amount, assets[asset]), p2.address())
                tid = self._transact(payer, refs2, outputs2, p2)
                self._deliver(payer, p2, tid, [model.ref(tid, 0)])
                return "ok"
            finally:
                payer._chaos_on_release = None
                for p in proxies:
                    p.deliver_held(lambda m_, b_: mine(m_, b_))

    # ------------------------------------------------------------ operator

    def _publish(self, cid: str, urls: list, committee: list) -> None:
        with self.dir_lock:
            self.directory[cid] = list(urls)
            if committee:
                self.committees[cid] = list(committee)
            else:
                self.committees.pop(cid, None)
        for name, w in list(self.wallets.items()) + [("mallory", self.mallory)]:
            with self._locked(name):
                net = w.network
                net.urls[cid] = list(urls)
                net.committees[cid] = list(committee or [])
                net._clients.clear()
                net._standbys.clear()
                net.refresh_charters(cid)

    def _start_new(self, idx: list) -> list:
        for i in idx:
            self._register_pk(i)
        for i in idx:
            self.c.start(i)
        for i in idx:
            self.c.wait_ready(i)
        for i in idx:
            self.c.witnesses[i]["pending"] = False
        return [self.c.url(i) for i in idx]

    def op_rotate(self, r: random.Random) -> str:
        with self.op_lock:
            plain = [cid for cid in self.cids if cid not in self.committees]
            if not plain:
                return "no-target"
            cid = r.choice(plain)
            n = len(self.c.indices(cid))
            new_idx = self.c.add_members(cid, self._kinds(r.choice([4, n])))
            new_urls = self._start_new(new_idx)
            old_idx = [i for i in range(len(self.c.witnesses)) if self.c.witnesses[i]["cid"] == cid
                       and self.c.url(i) in self.directory[cid]]
            if self.cfg.hooks:
                for i in r.sample(old_idx, min(len(old_idx), r.randint(0, 2))):
                    self._arm(i, "freeze", r)
                for i in r.sample(new_idx, r.randint(0, 2)):
                    self._arm(i, "adopt", r)
            net = RemoteNetwork({cid: list(self.directory[cid])}, timeout=self.cfg.client_timeout + 2)
            for attempt in range(12):
                try:
                    v = net.rotate(cid, new_urls, TOKEN)
                    break
                except RotationIncomplete as e:
                    self.faults["rotation-incomplete"] += 1
                    v = self._finish_rotation(net, cid, e.pending)
                    break
                except (RuntimeError, Rejected) as e:
                    self.log(f"rotation attempt {attempt}: {e}")
                    self.faults["rotation-retry"] += 1
                    self._restart_down(old_idx + new_idx)
                    time.sleep(1)
            else:
                return "failed"
            chain = net.registry.chain(cid)
            self.c.write_chain(cid, chain)
            self._publish(cid, new_urls, [])
            self.log(f"rotated {cid[:8]} to v{v} ({[self.c.witnesses[i]['kind'] for i in new_idx]})")
            return "ok"

    def _finish_rotation(self, net, cid: str, pending: list) -> int:
        chain = net.registry.chain(cid)
        nxt = chain[-1]["body"]
        for attempt in range(20):
            snaps, still = [], []
            for url in self.directory[cid]:
                try:
                    sig, snap = RemoteWitness(url, 5, admin_token=TOKEN).freeze(nxt)
                except Rejected:
                    continue
                snaps.append(snap)
            for url in pending:
                try:
                    RemoteWitness(url, 5).gossip({"charters": {cid: chain}})
                    w = RemoteWitness(url, 5, admin_token=TOKEN)
                    if w.cid is None:
                        w.adopt(cid, nxt["version"], snaps)
                except Rejected:
                    still.append(url)
            if not still:
                return nxt["version"]
            pending = still
            self._restart_down(range(len(self.c.witnesses)))
            time.sleep(1)
        raise RuntimeError("rotation never completed")

    def op_succession(self, r: random.Random) -> str:
        cid = self.cids[0]
        if cid not in self.committees:
            return "no-committee"
        with self.op_lock:
            home = [i for i in range(len(self.c.witnesses)) if self.c.witnesses[i]["cid"] == cid
                    and self.c.witnesses[i].get("role") != "standby" and self.c.url(i) in self.directory[cid]]
            # The home keeps serving wallets; only the standby members stop hearing it.
            for i in home:
                self.c.probes[i].faults.partition = r.choice(["refuse", "blackhole"])
            self.faults["probe-partition-past-dead-man"] += 1
            new_idx = self.c.add_members(cid, self._kinds(4))
            new_urls = self._start_new(new_idx)
            members = [self.c.probe_url(i) for i in new_idx]
            nk = self.c.add_standbys(cid, self._kinds(4))
            for i in nk:
                self.c.witnesses[i]["args"] += ["--members", *members, "--probe-every", str(self.cfg.probe_every)]
            new_k = self._start_new(nk)
            if self.cfg.hooks:
                for i in r.sample([j for j in self.c.indices(cid, role="standby") if j not in nk], r.randint(0, 2)):
                    self._arm(i, "succeed", r)
                for i in r.sample(nk, r.randint(0, 1)):
                    self._arm(i, "standby", r)
                for i in r.sample(new_idx, r.randint(0, 1)):
                    self._arm(i, "adopt", r)
            time.sleep(self.cfg.dead_man + 1.5)
            net = RemoteNetwork({cid: list(self.directory[cid])}, committees={cid: list(self.committees[cid])},
                                timeout=self.cfg.client_timeout + 2)
            v = None
            try:
                for attempt in range(15):
                    try:
                        v = net.succeed(cid, new_urls, TOKEN, committee_urls=new_k, dead_man=self.cfg.dead_man)
                        break
                    except RotationIncomplete as e:
                        self.faults["succession-incomplete"] += 1
                        v = self._finish_succession(net, cid, e.pending)
                        break
                    except (RuntimeError, Rejected) as e:
                        self.log(f"succession attempt {attempt}: {e}")
                        self._restart_down(range(len(self.c.witnesses)))
                        time.sleep(1)
            finally:
                for i in home:
                    self.c.probes[i].faults.partition = None
            if v is None:
                for i in new_idx + nk:
                    self.c.kill(i)
                    self.c.retired.add(i)
                return "failed"
            chain = net.registry.chain(cid)
            self.c.write_chain(cid, chain)
            self._publish(cid, new_urls, new_k)
            self.log(f"succession of {cid[:8]} to v{v}")
            return "ok"

    def _finish_succession(self, net, cid: str, pending: list) -> int:
        chain = net.registry.chain(cid)
        nxt = chain[-1]["body"]
        for attempt in range(20):
            snaps, still = [], []
            for url in self.committees[cid]:
                try:
                    sig, snap = RemoteStandby(url, 5, admin_token=TOKEN).succeed(nxt)
                except Rejected:
                    continue
                snaps.append(snap)
            for url in pending:
                try:
                    RemoteWitness(url, 5).gossip({"charters": {cid: chain}})
                    info = RemoteStandby(url, 5).info()
                    if info.get("role") == "standby":
                        m = RemoteStandby(url, 5, admin_token=TOKEN)
                        if m.version != nxt["version"]:
                            m.enter(cid, nxt["version"], snaps)
                    else:
                        w = RemoteWitness(url, 5, admin_token=TOKEN)
                        if w.cid is None:
                            w.adopt(cid, nxt["version"], snaps)
                except Rejected:
                    still.append(url)
            if not still:
                return nxt["version"]
            pending = still
            self._restart_down(range(len(self.c.witnesses)))
            time.sleep(1)
        raise RuntimeError("succession never completed")

    # ------------------------------------------------------------ chaos

    def _crash(self, i: int, downtime: float) -> None:
        if i in self.c.retired:
            return
        self.c.kill(i)
        self.faults["sigkill"] += 1
        t = threading.Timer(downtime, self._restart_one, args=(i,))
        t.daemon = True
        self.restart_timers.append(t)
        t.start()

    def _restart_one(self, i: int) -> None:
        if self.stop.is_set() or i in self.c.retired:
            return
        if not self.c.restart(i):
            self.log(f"{self.c.witnesses[i]['name']} did not restart")
            self.faults["restart-failed"] += 1

    def _restart_down(self, idx) -> None:
        for i in idx:
            if i in self.c.retired or self.c.alive(i):
                continue
            if self.c.witnesses[i].get("pending"):
                continue
            self.c.restart(i)

    def _arm(self, i: int, method: str, r: random.Random) -> None:
        phase = r.choice(["before", "during", "during", "after"])
        delay = r.choice([0.0, 0.001, 0.003, 0.01, 0.03])
        downtime = r.uniform(0.2, 2.5)
        fired = []

        def hook(proxy, m, body):
            if m != method or fired:
                return None
            fired.append(1)
            self.faults[f"kill-{phase}-{method}"] += 1
            return (phase, delay, lambda: self._crash(i, downtime))

        self.c._ensure_proxies(i)
        self.c.proxies[i].kill_hook = hook

    def chaos_loop(self) -> None:
        cfg, c = self.cfg, self.c
        r = random.Random(cfg.seed * 7919 + 1)
        episodes: list = []   # (end time, undo)
        methods_w = ["spend", "spend", "status", "release", "heartbeat"]
        methods_k = ["mirror", "mirror", "note_release"]
        while not self.stop.is_set():
            time.sleep(r.uniform(0.15, 0.6) / max(cfg.chaos_rate, 0.01))
            now = time.monotonic()
            for e in [e for e in episodes if e[0] <= now]:
                episodes.remove(e)
                try:
                    e[1]()
                except Exception as ex:  # noqa: BLE001
                    self.log(f"undo failed: {ex!r}")
            procs = [i for i in range(len(c.witnesses)) if i not in c.retired and not c.witnesses[i].get("pending")]
            if not procs:
                continue
            roll = r.random()
            i = r.choice(procs)
            standby = c.witnesses[i].get("role") == "standby"
            if roll < 0.12 and cfg.kills:
                if c.alive(i):
                    self._crash(i, r.uniform(0.1, 3.0))
            elif roll < 0.25 and cfg.hooks:
                self._arm(i, r.choice(methods_k if standby else methods_w), r)
            elif roll < 0.50 and cfg.net_faults:
                p = c.proxies[i]
                f = p.faults
                f.p_drop = r.choice([0, 0, 0.1, 0.3])
                f.p_lose_reply = r.choice([0, 0, 0.1, 0.3])
                f.p_delay = r.choice([0, 0.3, 0.6])
                f.delay = (0.01, r.choice([0.2, 1.0, cfg.client_timeout * 2]))
                f.p_dup = r.choice([0, 0, 0.2, 0.5])
                f.p_hold = r.choice([0, 0, 0, 0.1])
                self.faults["net-fault-episode"] += 1
                episodes.append((now + r.uniform(1, 6), f.clear))
            elif roll < 0.60 and cfg.partitions:
                cid = c.witnesses[i]["cid"]
                group = [j for j in procs if c.witnesses[j]["cid"] == cid]
                k = r.choice([1, 1, 2, max(1, len(group) // 2)])
                part = r.sample(group, min(k, len(group)))
                mode = r.choice(["refuse", "blackhole"])
                which = r.choice(["client", "client", "probe"])
                ps = [c.probes[j] if which == "probe" and j in c.probes else c.proxies[j] for j in part]
                for p in ps:
                    p.faults.partition = mode
                self.faults[f"partition-{which}"] += 1

                def heal(ps=ps):
                    for p in ps:
                        p.faults.partition = None
                episodes.append((now + r.uniform(0.5, cfg.dead_man * 1.8), heal))
            elif roll < 0.66:
                for p in c.all_proxies():
                    if p.held and r.random() < 0.5:
                        self.faults["held-delivered-late"] += p.deliver_held()
            elif roll < 0.72 and self.skew_so is not None and not standby and i not in self.byz_idx:
                if cfg.skew in ("within", "beyond_f"):
                    if i in self.faulty_clock:
                        c.set_skew(i, -r.randint(cfg.max_skew + 2, 4 * cfg.max_skew))
                    else:
                        c.set_skew(i, r.randint(-(cfg.max_skew - 1), cfg.pledge_ttl // 2))
                    self.faults["clock-skew-change"] += 1
            elif roll < 0.76 and cfg.disk and not standby and i not in self.byz_idx and i not in c.disk_full:
                how = c.fill_disk(i)
                if how:
                    self.faults[f"disk-full-{how}"] += 1

                    def free(i=i):
                        c.free_disk(i)
                        if not c.alive(i) and i not in c.down:
                            self.faults["died-on-full-disk"] += 1
                            c.down.add(i)
                        if not c.alive(i):
                            self._restart_one(i)
                    episodes.append((now + r.uniform(0.5, 4), free))
        for e in episodes:
            try:
                e[1]()
            except Exception:  # noqa: BLE001
                pass

    # ------------------------------------------------------------ workload

    def worker(self, k: int, plan: list) -> None:
        r = random.Random(self.cfg.seed * 104729 + k)
        for op in plan:
            if self.stop.is_set():
                return
            fn = getattr(self, "op_" + op)
            try:
                outcome = fn(r)
                self.ops[f"{op}:{outcome}"] += 1
            except EXPECTED as e:
                self.ops[f"{op}:{type(e).__name__}"] += 1
            except Exception as e:  # noqa: BLE001 - classified as an anomaly
                self.ops[f"{op}:anomaly"] += 1
                self.anomaly(op, e)

    def plan(self) -> list:
        cfg, r = self.cfg, random.Random(self.cfg.seed * 31337)
        weights = {"pay": 10, "swap": 2, "settle": 2, "mallory": 2 if cfg.mallory else 0}
        names = [k for k, v in weights.items() for _ in range(v)]
        ops = [r.choice(names) for _ in range(cfg.ops)]
        specials = ["delayed_expiry"] * cfg.delayed_expiry
        if cfg.rotation:
            specials.append("rotate")
        if cfg.succession and cfg.committee:
            specials.append("succession")
        for s in specials:
            ops.insert(r.randrange(len(ops) + 1), s)
        per = [[] for _ in range(max(1, cfg.workers))]
        for j, op in enumerate(ops):
            per[j % len(per)].append(op)
        return per

    def run(self) -> dict:
        try:
            self.setup()
            chaos = threading.Thread(target=self.chaos_loop, daemon=True)
            chaos.start()
            plans = self.plan()
            ts = [threading.Thread(target=self.worker, args=(k, p), daemon=True) for k, p in enumerate(plans)]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            self.stop.set()
            chaos.join()
            self.heal()
            self.settle()
            self.check()
        except Exception as e:  # noqa: BLE001
            self.anomaly("harness", e)
        finally:
            self.stop.set()
            self.finish()
        return self.result

    # ------------------------------------------------------------ heal / settle

    def heal(self) -> None:
        c = self.c
        for t in self.restart_timers:
            t.cancel()
        for p in c.all_proxies():
            p.faults.clear()
            p.kill_hook = None
        for i in list(c.disk_full):
            c.free_disk(i)
        for i in range(len(c.witnesses)):
            if i not in self.faulty_clock:
                c.set_skew(i, 0)
        own = c.crashed_on_its_own()
        if own:
            self.faults["exited-unkilled"] += len(own)
            self.log(f"processes that exited on their own: {[c.witnesses[i]['name'] for i in own]}")
        for i in range(len(c.witnesses)):
            if i in c.retired or c.alive(i):
                continue
            if not c.restart(i):
                self.liveness.append({"kind": "restart-failed", "process": c.witnesses[i]["name"]})
        n = sum(p.deliver_held() for p in c.all_proxies())
        self.faults["held-delivered-at-heal"] += n
        self.log("healed")

    def settle(self) -> None:
        deadline = time.monotonic() + self.cfg.liveness_bound
        # Undelivered payments first (the parcel is the payee's).
        while time.monotonic() < deadline:
            busy = False
            for name, w in self.wallets.items():
                w.release_expired_pledges()
                self._deliver_completed(w)
                if self._live_pledges(w):
                    busy = True
            todo, self.undelivered = self.undelivered, []
            for payer, payee, tid, refs in todo:
                if not self._deliver(self.wallets[payer], self.wallets[payee], tid, refs):
                    busy = True
            self._settle_swaps()
            if not busy:
                break
            time.sleep(1.0)
        for name, w in self.wallets.items():
            for s, (g, tid, exp) in self._live_pledges(w).items():
                self.liveness.append({"kind": "pledge-unsettled", "wallet": name, "sigil": s, "gen": g, "tid": tid,
                                      **self._diagnose(w, s, g, tid)})
        for payer, payee, tid, refs in self.undelivered:
            self.liveness.append({"kind": "payment-undelivered", "payer": payer, "payee": payee, "tid": tid})
        # Every wallet with funds can pay again.
        names = list(self.wallets)
        for k, name in enumerate(names):
            w, to = self.wallets[name], self.wallets[names[(k + 1) % len(names)]]
            assets = self._holding_asset(w)
            if not assets:
                continue
            asset = sorted(assets)[0]
            ok, err = False, None
            while time.monotonic() < deadline + 60 and not ok:
                try:
                    refs, outputs = w.payment_outputs(asset, 1, to.address())
                    tid = self._transact(w, refs, outputs, to)
                    ok = self._deliver(w, to, tid, [model.ref(tid, 0)])
                except EXPECTED as e:
                    err = repr(e)
                    w.release_expired_pledges()
                    time.sleep(1)
                except Exception as e:  # noqa: BLE001
                    self.anomaly("final-payment", e)
                    break
            self.ops["final-payment:" + ("ok" if ok else "failed")] += 1
            if not ok:
                self.liveness.append({"kind": "final-payment-failed", "wallet": name, "error": err})
        # deliveries of the final payments
        todo, self.undelivered = self.undelivered, []
        for payer, payee, tid, refs in todo:
            if not self._deliver(self.wallets[payer], self.wallets[payee], tid, refs):
                self.liveness.append({"kind": "payment-undelivered", "payer": payer, "payee": payee, "tid": tid})

    @staticmethod
    def _live_pledges(w: Wallet) -> dict:
        """Pledges of parcels the wallet still holds. (``Wallet.finalise`` leaves the pledges of
        consumed inputs in ``pledged``; they are inert, since a consumed sigil is never reused.)"""
        held = {h["sigil"] for h in w.holdings.values()}
        return {s: p for s, p in w.pledged.items() if s in held}

    def _diagnose(self, w: Wallet, s: str, g: int, tid: str) -> dict:
        """Why a pledge did not settle: what each member says, and what the tid was."""
        h = next((h for h in w.holdings.values() if h["sigil"] == s), None)
        out = {"held": h is not None, "pending": tid in w.pending,
               "swap": any(t == tid for *_, t in self.swaps), "payment": tid in self.payee_of,
               "kill_switch": s in w.kill_switches, "now_minus_expiry": int(time.time()) - w.pledged[s][2]}
        if h is not None:
            sts = []
            for rw in w.network.all_witnesses(h["parcel"]["home"]):
                try:
                    st = rw.status(s)
                    sts.append([rw.pk[:8], st.get("gen"), (st.get("tid") or "")[:8],
                                [(v["gen"], v["tid"][:8]) for v in st.get("votes", [])]])
                except Exception as e:  # noqa: BLE001
                    sts.append([rw.pk[:8], repr(e)[:80]])
            out["status"] = sts
        return out

    def _settle_swaps(self) -> None:
        """A swap interrupted after sealing: hand the seals to the party that lacks them."""
        for a_name, b_name, header, body, tid in self.swaps:
            a, b = self.wallets[a_name], self.wallets[b_name]
            done = [w for w in (a, b) if tid in w.dossier.transitions]
            if not done or len(done) == 2:
                continue
            src = done[0]
            dst = b if src is a else a
            if not any(model.parcel_id(r) in dst.holdings for r in body["inputs"]):
                continue
            dst.dossier.merge(src.dossier.ancestry([tid]))
            unlocks = src.dossier.transitions[tid]["unlocks"]
            dst.finalise(header, body, unlocks)
            for s, _g in header["inputs"]:
                dst.pledged.pop(s, None)
            self.ops["swap-handed-over"] += 1

    # ------------------------------------------------------------ checks

    def final_status(self) -> dict:
        sigils = set()
        for h in list(self.obs.headers.values()):
            for s, _g in h.get("inputs", []):
                sigils.add(s)
        for w in list(self.wallets.values()) + [self.mallory]:
            for tx in w.dossier.transitions.values():
                for s, _g in tx["header"]["inputs"]:
                    sigils.add(s)
        out = {}

        def sweep(i):
            name = self.c.proxies[i].name
            res = {}
            try:
                rw = RemoteWitness(self.c.real_url(i), 10)
                for s in sigils:
                    st = rw.status(s)
                    res[s] = st
                    for v in st.get("votes", []):
                        self.obs.add_vote(v)
            except Rejected as e:
                return name, None, repr(e)
            return name, res, None

        idx = [i for i in self._honest_witnesses() if self.c.alive(i)]
        with ThreadPoolExecutor(8) as ex:
            for name, res, err in ex.map(sweep, idx):
                if res is not None:
                    out[name] = res
                else:
                    self.liveness.append({"kind": "status-sweep-failed", "process": name, "error": err})
        return out

    def check(self) -> None:
        c = self.c
        registry = Registry()
        with open(c.registry) as f:
            for cid, chain in json.load(f).items():
                registry.add_chain(cid, chain)
        for w in self.wallets.values():
            for cid in registry.ids():
                if len(w.network.registry.chain(cid)) > len(registry.chain(cid)):
                    registry.add_chain(cid, w.network.registry.chain(cid))
        final = self.final_status()
        honest = {c.witnesses[i]["pk"] for i in self._honest_witnesses()}
        clocked = {c.witnesses[i]["pk"] for i in self._honest_witnesses()
                   if i not in self.faulty_clock}
        extra_seals, extra_headers = [], {}
        for w in list(self.wallets.values()) + [self.mallory]:
            extra_seals += list(w.dossier.seals.values())
            for tid, tx in w.dossier.transitions.items():
                extra_headers[tid] = tx["header"]
        self.violations += invariants.check(self.obs, registry, honest=honest, clocked=clocked,
                                            released=self.released, final_status=final,
                                            extra_seals=extra_seals, extra_headers=extra_headers)
        self._check_wallets(registry)

    def _check_wallets(self, registry) -> None:
        # S3: supply conserved per honest asset; nothing credited twice.
        totals = Counter()
        seen: dict = {}
        for name, w in self.wallets.items():
            for pid, h in w.holdings.items():
                p = h["parcel"]
                if p["asset"] in self.assets and locks.keys_in(p["lock"]) & set(w.keys):
                    totals[p["asset"]] += p["amount"]
                if h["sigil"] in seen and seen[h["sigil"]] != name:
                    self.violations.append({"kind": "S3-parcel-held-twice", "sigil": h["sigil"],
                                            "wallets": [seen[h["sigil"]], name]})
                seen[h["sigil"]] = name
        in_transit = Counter()
        for payer, payee, tid, refs in self.undelivered:
            for r in refs:
                p = self.wallets[payer].dossier.output(r)
                in_transit[p["asset"]] += p["amount"]
        for asset, supply in self.assets.items():
            got = totals[asset] + in_transit[asset]
            if got > supply:
                self.violations.append({"kind": "S3-inflation", "asset": asset, "supply": supply, "held": got})
            elif got < supply:
                self.liveness.append({"kind": "S3-value-not-accounted", "asset": asset, "supply": supply,
                                      "held": totals[asset], "in_transit": in_transit[asset]})
        # S4: every honest holding verifies with a fresh verifier, and is not consumed.
        sealed = self.obs.seals(registry, [s for w in self.wallets.values() for s in w.dossier.seals.values()])
        consumed = {}
        headers = dict(self.obs.headers)
        for w in self.wallets.values():
            for tid, tx in w.dossier.transitions.items():
                headers[tid] = tx["header"]
        sealed_set = {(s, g, t) for (s, g), ts in sealed.items() for t in ts}
        for t, h in headers.items():
            if h.get("inputs") and all((s, g, t) in sealed_set for s, g in h["inputs"]):
                for s, _g in h["inputs"]:
                    consumed[s] = t
        policy = TrustPolicy(registry, set(registry.ids()))
        for name, w in self.wallets.items():
            fresh = Verifier(policy)
            for h in w.holdings.values():
                try:
                    fresh.verify_parcel(w.dossier, h["ref"])
                except InvalidDossier as e:
                    self.violations.append({"kind": "S4-holding-does-not-verify", "wallet": name,
                                            "ref": h["ref"], "error": str(e)})
                if h["sigil"] in consumed and h["sigil"] not in w.pledged:
                    self.violations.append({"kind": "S4-holding-already-consumed", "wallet": name,
                                            "sigil": h["sigil"], "by": consumed[h["sigil"]]})

    def finish(self) -> None:
        stats: Counter = Counter()
        for p in self.c.all_proxies():
            stats.update(p.stats)
        self.result = {
            "seed": self.cfg.seed,
            "config": asdict(self.cfg),
            "duration": round(time.monotonic() - self.started, 1),
            "ops": dict(self.ops),
            "faults": dict(self.faults),
            "proxy": dict(stats),
            "kills": self.c.kills,
            "votes_observed": len(self.obs.votes),
            "transitions_observed": len(self.obs.headers),
            "violations": self.violations,
            "liveness": self.liveness,
            "anomalies": self.anomalies,
            "dir": self.tmp,
        }
        try:
            self.c.teardown()
        finally:
            if not self.keep and not (self.violations and os.environ.get("SIGIL_CHAOS_KEEP_FAILED")):
                shutil.rmtree(self.tmp, ignore_errors=True)


def summarize(results: list) -> dict:
    agg = {"runs": len(results), "duration": 0.0, "ops": Counter(), "faults": Counter(), "proxy": Counter(),
           "kills": 0, "votes_observed": 0, "violations": Counter(), "liveness": Counter(), "anomalies": Counter(),
           "seeds_with_violations": [], "seeds_with_liveness_failures": [], "seeds_with_anomalies": []}
    for r in results:
        agg["duration"] += r["duration"]
        agg["ops"].update(r["ops"])
        agg["faults"].update(r["faults"])
        agg["proxy"].update(r["proxy"])
        agg["kills"] += r["kills"]
        agg["votes_observed"] += r["votes_observed"]
        for v in r["violations"]:
            agg["violations"][v["kind"]] += 1
        for v in r["liveness"]:
            agg["liveness"][v["kind"]] += 1
        for a in r["anomalies"]:
            agg["anomalies"][a["key"]] += 1
        if r["violations"]:
            agg["seeds_with_violations"].append(r["seed"])
        if r["liveness"]:
            agg["seeds_with_liveness_failures"].append(r["seed"])
        if r["anomalies"]:
            agg["seeds_with_anomalies"].append(r["seed"])
    for k in ("ops", "faults", "proxy", "violations", "liveness", "anomalies"):
        agg[k] = dict(agg[k])
    agg["duration"] = round(agg["duration"], 1)
    return agg


def _seeds(spec: str) -> list:
    out = []
    for part in spec.split(","):
        if "-" in part:
            a, b = part.split("-")
            out += list(range(int(a), int(b) + 1))
        elif part:
            out.append(int(part))
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Sigil chaos runs")
    ap.add_argument("--seeds", default="1-3")
    ap.add_argument("--minutes", type=float, default=None, help="keep running new seeds until this much time passed")
    ap.add_argument("--ops", type=int, default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--set", action="append", default=[], help="config override key=json")
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args(argv)
    if not rust_available():
        print(f"{RUST_BIN} missing: cargo build --release --locked in rust/", file=sys.stderr)
        return 2
    over = {}
    for kv in a.set:
        k, v = kv.split("=", 1)
        over[k] = json.loads(v)
    if a.ops is not None:
        over["ops"] = a.ops
    seeds = _seeds(a.seeds)
    t0 = time.monotonic()
    results = []
    k = 0
    while True:
        if k < len(seeds):
            seed = seeds[k]
        elif a.minutes is not None and time.monotonic() - t0 < a.minutes * 60:
            seed = seeds[-1] + 1 + (k - len(seeds))
        else:
            break
        k += 1
        cfg = Config.random(seed, **over)
        res = ChaosRun(cfg, keep=a.keep, log=print if a.v else None).run()
        results.append(res)
        print(json.dumps({"seed": seed, "duration": res["duration"], "ops": sum(res["ops"].values()),
                          "kills": res["kills"], "violations": [v["kind"] for v in res["violations"]],
                          "liveness": [v["kind"] for v in res["liveness"]],
                          "anomalies": [x["key"] for x in res["anomalies"]]}), flush=True)
        if a.out:
            with open(a.out, "w") as f:
                json.dump({"summary": summarize(results), "runs": results}, f, indent=1, default=str)
    print(json.dumps(summarize(results), indent=1, default=str))
    return 1 if any(r["violations"] for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
