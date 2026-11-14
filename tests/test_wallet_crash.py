"""Wallet crashes at every step, restarted from ``sigil.wallet_store`` (exhaustive, in process).

A wallet process can die between any two calls it makes: before a request leaves, after a
witness processed it but before the reply arrived, or in the middle of writing its directory
(``wallet_store.save`` writes keys, dossier and state as three files). Each test runs one
operation once to count its *crash points* (every witness / standby call, before and after it is
served, and every file write of a save), then, for each point, runs the operation again from the
same start, kills the wallet there (a ``BaseException`` no wallet code catches, like SIGKILL),
reloads every wallet of the operation from its directory as the application left it, lets time
pass and settles: ``release_expired_pledges``, handing out completed payments, receiving them.
After settling it checks:

* **no self-equivocation**: across all witnesses, at most one tid was ever bound or voted at any
  ``(sigil, gen)`` of an honest wallet (SPEC §4 rule 1; a rule-3 release leaves no binding);
* **no lost and no double funds**: per asset, the parcels held by the wallets plus the payments
  handed out but not yet received add up to the supply exactly; no sigil is held twice, and every
  unpledged holding is unspent at its home;
* **eventual settlement**: no live pledge is left, and each wallet can pay again.

The application's save points follow ``sigil.cli``: ``on_pledge`` saves every authorisation
before any witness sees it, and the application saves after every operation. Operations: pay
(``sigil.cli cmd_pay`` / ``cmd_receive``, which write and read payment files), consolidate,
``atomic_swap``, ``propose_swap`` + ``cosign`` driven by hand, ``abort`` after a counter-party
double spend, and ``release_expired_pledges`` of a pledge whose payment failed.

By default 40 crash points per operation run (about 40 s in all); ``SIGIL_CRASH_POINTS=all``
runs every one of them (a few minutes).
"""

import json
import os
import shutil
import tempfile
import unittest
from collections import Counter, defaultdict

from sigil import cli, model, wallet_store
from sigil.charter import faults, quorum
from sigil.locks import keys_in
from sigil.network import Network
from sigil.swap import atomic_swap, propose_swap
from sigil.validate import InvalidDossier, TrustPolicy, Verifier
from sigil.wallet import SealFailed, Wallet
from sigil.witness import Rejected

TTL, SKEW = 60, 10
CALLS = ("spend", "status", "release", "mirror_bind", "note_release")


class Crash(BaseException):
    """The wallet process dies here."""


class Points:
    def __init__(self, armed=None):
        self.n = 0
        self.armed = armed         # (index, "before" | "after"), counted from ``begin``
        self.crash_at = None

    def begin(self) -> None:
        """The crashable part of an operation starts here (setup before it never crashes)."""
        self.n, self.crash_at = 0, self.armed

    def hit(self, phase: str) -> None:
        if self.crash_at is not None and (self.n, phase) == self.crash_at:
            self.crash_at = None
            raise Crash(f"crash {phase} point {self.n}")


class Proxy:
    def __init__(self, target, points):
        self._t, self._p = target, points

    def __getattr__(self, name):
        attr = getattr(self._t, name)
        if name not in CALLS:
            return attr

        def call(*a, **kw):
            p = self._p
            p.n += 1
            p.hit("before")
            out = attr(*a, **kw)
            p.hit("after")
            return out
        return call


class CrashNet:
    """A ``Network`` whose witnesses and standby members count (and crash at) every call."""

    def __init__(self, net: Network, points: Points):
        self._net, self.points = net, points

    def __getattr__(self, name):
        return getattr(self._net, name)

    def witnesses(self, cid):
        return [Proxy(w, self.points) for w in self._net.witnesses(cid)]

    def all_witnesses(self, cid):
        return [Proxy(w, self.points) for w in self._net.all_witnesses(cid)]

    def committee(self, cid):
        return [Proxy(m, self.points) for m in self._net.committee(cid)]

    def find_votes(self, sigil):
        self.points.n += 1
        self.points.hit("before")
        return self._net.find_votes(sigil)


_ATOMIC_WRITE = wallet_store._atomic_write


class _CountingJson:
    def __init__(self, points):
        self._p = points

    def __getattr__(self, name):
        return getattr(json, name)

    def dump(self, *a, **kw):
        self._p.n += 1
        self._p.hit("before")
        return json.dump(*a, **kw)


class World:
    """One run: a network (two homes, the first with a successor committee), wallets in
    directories, and the payment files handed out."""

    def __init__(self, tmp: str, points: Points):
        self.tmp, self.points = tmp, points
        self.net = Network()
        self.X = self.net.create_constellation("orion", 4, successor={"n": 4, "dead_man": 10_000})
        self.Y = self.net.create_constellation("lyra", 4)
        self.cnet = CrashNet(self.net, points)
        cli._network = lambda _path: self.cnet   # the CLI's wallets talk to this network
        cli.json = _CountingJson(points)         # writing a payment file is a crash point too

        def counted(path, data, mode=0o600, _orig=_ATOMIC_WRITE):   # and every file a save writes
            points.n += 1
            points.hit("before")
            _orig(path, data, mode)
        wallet_store._atomic_write = counted
        self.supply: dict = {}
        self.outbox = os.path.join(tmp, "payments")
        os.makedirs(self.outbox)
        self.wallets: dict = {}
        for name, home in (("alice", self.X), ("bob", self.Y), ("carol", self.X)):
            w = Wallet(name, self.cnet, home, pledge_ttl=TTL, max_skew=SKEW)
            self._hook(w)
            self.wallets[name] = w
            a = w.issue(name.upper(), 100)
            self.supply[a] = 100
            self.save(name)
        self.pending_files: set = set()

    def dir(self, name):
        return os.path.join(self.tmp, name)

    def _hook(self, w):
        name = w.name
        w.on_pledge = lambda _w: self.save(name)

    def save(self, name):
        wallet_store.save(self.wallets[name], self.dir(name))

    def reload(self, names):
        for name in names:
            w = wallet_store.load(self.dir(name), self.cnet)
            self._hook(w)
            self.wallets[name] = w

    def begin(self):
        self.points.begin()

    def asset_of(self, name):
        return next(x for x in self.supply if self._name_of(x) == name.upper())

    def _name_of(self, a):
        for w in self.wallets.values():
            tx = w.dossier.transitions.get(a)
            if tx:
                return tx["body"]["genesis"]["name"]
        return None

    # ------------------------------------------------------------ the CLI, in process

    def cli_args(self, name, **kw):
        class A:
            pass
        a = A()
        a.wallet, a.directory = self.dir(name), "unused"
        for k, v in kw.items():
            setattr(a, k, v)
        return a

    def cli_pay(self, payer, payee, asset, amount):
        """``sigil address`` at the payee, then ``sigil pay`` at the payer (file hand-off)."""
        addr = cli.cmd_address(self.cli_args(payee, home=None))
        apath = os.path.join(self.tmp, f"addr-{payee}-{len(os.listdir(self.tmp))}.json")
        with open(apath, "w") as f:
            json.dump(addr, f)
        out = os.path.join(self.outbox, f"pay-{len(os.listdir(self.outbox))}.json")
        res = cli.cmd_pay(self.cli_args(payer, address=apath, asset=asset, amount=amount, out=out))
        return res

    # ------------------------------------------------------------ settling and checks

    def settle(self, rounds: int = 4):
        """Time passes; each wallet settles (as the CLI does before every payment) and every
        payment file handed out is received."""
        self.points.crash_at = self.points.armed = None
        for _ in range(rounds):
            self.net.clock.advance(TTL + SKEW + 1)
            for name in self.wallets:
                w = wallet_store.load(self.dir(name), self.cnet)
                self._hook(w)
                self.wallets[name] = w
                w.release_expired_pledges()
                cli._hand_out_completed(w, self.cli_args(name, out=os.path.join(self.outbox, f"retry-{name}")))
                self.save(name)
            # The parties of a multi-party transition hand a completed one to each other.
            for name, w in self.wallets.items():
                for tid in list(w.pending):
                    other = next((o for o in self.wallets.values() if o is not w and tid in o.dossier.transitions),
                                 None)
                    if other is not None:
                        w.accept_completed(other.dossier, tid)
                        self.save(name)
            self.receive_all()

    def receive_all(self):
        for fn in sorted(os.listdir(self.outbox)):
            path = os.path.join(self.outbox, fn)
            try:
                with open(path) as f:
                    obj = json.load(f)
            except ValueError:
                continue   # a truncated payment file: the payee cannot use it (the funds are lost)
            d = cli.Dossier.from_json(json.dumps(obj["dossier"]))
            for r in obj["refs"]:
                p = d.output(r)
                s = model.sigil_of(p)
                owner = next((n for n, w in self.wallets.items() if s in w.issued), None)
                if owner is None:
                    continue
                pf = os.path.join(self.tmp, "received")
                done = set()
                if os.path.exists(pf):
                    with open(pf) as f:
                        done = set(f.read().split())
                if s in done:
                    continue
                try:
                    cli.cmd_receive(self.cli_args(owner, payment=path, deep=False))
                except InvalidDossier:
                    continue
                with open(pf, "a") as f:
                    f.write(s + "\n")

    def violations(self) -> list:
        out = []
        net = self.net
        # no self-equivocation, across every witness ever (old versions included)
        tids = defaultdict(set)
        for cid in net.members:
            for w in net.all_witnesses(cid) + net.retired.get(cid, []):
                for s, rec in w.records.items():
                    if rec.tid is not None and not rec.tid.startswith("!"):
                        tids[(s, rec.gen)].add(rec.tid)
                    for v in rec.votes:
                        tids[(s, v["gen"])].add(v["tid"])
        for (s, g), ts in tids.items():
            if len(ts) > 1:
                out.append(("self-equivocation", s[:12], g, sorted(t[:12] for t in ts)))
        # funds: held + handed out but not received == supply
        held = Counter()
        seen = {}
        for name, w in self.wallets.items():
            for h in w.holdings.values():
                p = h["parcel"]
                if p["asset"] in self.supply and keys_in(p["lock"]) & set(w.keys):
                    held[p["asset"]] += p["amount"]
                if h["sigil"] in seen:
                    out.append(("held-twice", h["sigil"][:12], seen[h["sigil"]], name))
                seen[h["sigil"]] = name
                if h["sigil"] not in w.pledged and self._consumed(h):
                    out.append(("holding-consumed", name, h["sigil"][:12]))
                try:   # every holding verifies from the wallet's own dossier, with a fresh verifier
                    Verifier(TrustPolicy(self.net.registry, set(self.net.registry.ids()))).verify_parcel(
                        w.dossier, h["ref"])
                except InvalidDossier as e:
                    out.append(("holding-does-not-verify", name, h["sigil"][:12], str(e)))
        for a, n in self.supply.items():
            if held[a] != n:
                out.append(("funds", self._name_of(a), held[a], n))
        for name, w in self.wallets.items():
            live = {h["sigil"] for h in w.holdings.values()} & set(w.pledged)
            if live:
                out.append(("unsettled", name, len(live)))
        return out

    def _consumed(self, h) -> bool:
        home = h["parcel"]["home"]
        votes = defaultdict(set)
        for w in self.net.all_witnesses(home):
            for v in w.status(h["sigil"])["votes"]:
                if v["gen"] == h["gen"]:
                    votes[v["tid"]].add(v["witness"])
        n = len(self.net.registry.latest(home)["witnesses"])
        return any(len(ws) >= quorum(n) for ws in votes.values())

    def can_pay(self) -> list:
        bad = []
        for name, w in self.wallets.items():
            a = next((a for a in self.supply if w.balance(a) > 0), None)
            if a is None:
                continue
            try:
                self.cli_pay(name, "carol" if name != "carol" else "alice", a, 1)
            except (SealFailed, ValueError) as e:
                bad.append((name, repr(e)))
        self.receive_all()
        return bad


def scenario_count(case, op) -> int:
    tmp = tempfile.mkdtemp(prefix="sigil-crash-")
    case.addCleanup(shutil.rmtree, tmp, ignore_errors=True)
    world = World(tmp, Points())
    op(world)
    return world.points.n


def run_crashes(case, op, names, limit=None):
    """Run ``op`` once per crash point; returns the failures as ``(point, violations)``."""
    total = scenario_count(case, op)
    failures = []
    points = [(i, ph) for i in range(1, total + 1) for ph in ("before", "after")]
    if limit is not None and len(points) > limit:
        step = len(points) / limit
        points = [points[int(k * step)] for k in range(limit)]
    for i, ph in points:
        tmp = tempfile.mkdtemp(prefix="sigil-crash-")
        try:
            world = World(tmp, Points((i, ph)))
            crashed = False
            try:
                op(world)
            except Crash:
                crashed = True
            except (SealFailed, ValueError, Rejected, InvalidDossier):
                pass
            if crashed:
                world.reload(names)
            world.settle()
            v = world.violations()
            if not v:
                v = [("cannot-pay-again", *x) for x in world.can_pay()]
            if v:
                failures.append(((i, ph, crashed), v))
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    return total, failures


# ------------------------------------------------------------ operations

def op_pay(world):
    world.begin()
    world.cli_pay("alice", "bob", world.asset_of("alice"), 30)


def op_consolidate(world):
    w = world.wallets["alice"]
    a = world.asset_of("alice")
    refs, outs = w.payment_outputs(a, 40, w.address())   # two parcels first
    w.transact(refs, outs)
    world.save("alice")
    world.begin()
    refs = [h["ref"] for h in w.holdings.values() if h["parcel"]["asset"] == a]
    total = sum(w.dossier.output(r)["amount"] for r in refs)
    me = w.address()
    world.save("alice")
    w.transact(refs, [model.parcel(me["home"], a, total, me["lock"], me["salt"])], memo="consolidate")
    world.save("alice")


def op_atomic_swap(world):
    a, b = world.wallets["alice"], world.wallets["bob"]
    world.begin()
    atomic_swap(a, world.asset_of("alice"), 10, b, world.asset_of("bob"), 20)
    world.save("alice")
    world.save("bob")


def op_manual_swap(world):
    """propose_swap, both authorise and cosign, bob drives the sealing (kill switches last)."""
    a, b = world.wallets["alice"], world.wallets["bob"]
    world.begin()
    header, body, _ = propose_swap(a, world.asset_of("alice"), 5, b, world.asset_of("bob"), 7)
    world.save("alice")
    world.save("bob")
    sig = {s for s, _ in header["inputs"]}
    unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
    for w in (a, b):
        w.cosign(header, unlocks)
    kills = (a.kill_switches | b.kill_switches) & sig
    b.seal(header, body, unlocks, only=sig - kills)
    unlocks.update({**a.authorise(header, body, release_kill=True), **b.authorise(header, body, release_kill=True)})
    for w in (a, b):
        w.cosign(header, unlocks)
    b.seal(header, body, unlocks, only=kills)
    tid = model.transition_id(header)
    a.dossier.merge(b.dossier.ancestry({r["tx"] for r in body["inputs"]}))
    for s in b.dossier.seals.values():
        if s["tid"] == tid:
            a.dossier.add_seal(s)
    for w in (a, b):
        w.finalise(header, body, unlocks)
    world.save("alice")
    world.save("bob")


def op_abort(world):
    """alice's input is bound to a swap; bob spends his own swap input elsewhere (a death proof
    for the swap); alice aborts and frees her input."""
    from sigil import locks
    from sigil.wallet import request_seal
    a, b = world.wallets["alice"], world.wallets["bob"]
    x, y = world.asset_of("alice"), world.asset_of("bob")
    header, body, _ = propose_swap(a, x, 5, b, y, 7)
    tid = model.transition_id(header)
    unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
    mine = {h["sigil"] for h in a.holdings.values()}
    a.seal(header, body, unlocks, only={s for s, _ in header["inputs"] if s in mine and s not in a.kill_switches})
    ref, sg = next((r, s) for r, (s, _g) in zip(body["inputs"], header["inputs"])
                   if any(h["sigil"] == s for h in b.holdings.values()) and s not in b.kill_switches)
    p = b.dossier.output(ref)
    me = b.address()
    hb, bb, tb = b.prepare([ref], [model.parcel(me["home"], p["asset"], p["amount"], me["lock"], me["salt"])],
                           memo="betray")
    exp = int(world.net.clock()) + TTL
    u = locks.empty_unlock(exp)
    for pk in keys_in(p["lock"]) & set(b.keys):
        u["sigs"][pk] = locks.sign_unlock(b.keys[pk], sg, tb, exp)
    b.dossier.add_seal(request_seal(world.net, {"sigil": sg, "header": hb, "home": p["home"], "lock": p["lock"],
                                                "salt": p["salt"], "unlock": u}))
    b.pledged.pop(sg, None)
    b.pending.pop(tid, None)
    b.finalise(hb, bb, {sg: u})
    world.save("alice")
    world.save("bob")
    world.begin()
    a.abort(header)
    world.save("alice")


def op_release_expired(world):
    """alice's payment to bob reached no witness (her home was unreachable); after expiry she
    settles the pledge."""
    w = world.wallets["alice"]
    addr = world.wallets["bob"].address()
    world.save("bob")
    refs, outs = w.payment_outputs(world.asset_of("alice"), 10, addr)
    world.net.down |= {x.pk for x in world.net.all_witnesses(world.X)}
    try:
        w.transact(refs, outs)
    except SealFailed:
        pass
    world.net.down.clear()
    world.save("alice")
    world.net.clock.advance(TTL + SKEW + 1)
    world.begin()
    w.release_expired_pledges()
    world.save("alice")


class WalletCrashes(unittest.TestCase):
    # Crash points per operation (spread evenly); SIGIL_CRASH_POINTS=all runs every one.
    _env = os.environ.get("SIGIL_CRASH_POINTS", "40")
    LIMIT = None if _env == "all" else int(_env)

    def setUp(self):
        self.addCleanup(setattr, cli, "_network", cli._network)
        self.addCleanup(setattr, cli, "json", cli.json)
        self.addCleanup(setattr, wallet_store, "_atomic_write", _ATOMIC_WRITE)

    def check(self, op, names):
        total, failures = run_crashes(self, op, names, self.LIMIT)
        self.assertGreater(total, 0)
        self.assertEqual(failures, [], f"{len(failures)} of {2 * total} crash points fail: {failures[:5]}")

    def test_pay_and_receive_with_the_cli(self):
        self.check(op_pay, ["alice", "bob"])

    def test_consolidate(self):
        self.check(op_consolidate, ["alice"])

    def test_atomic_swap(self):
        self.check(op_atomic_swap, ["alice", "bob"])

    def test_propose_swap_and_cosign(self):
        self.check(op_manual_swap, ["alice", "bob"])

    def test_abort(self):
        self.check(op_abort, ["alice"])

    def test_release_expired_pledges(self):
        self.check(op_release_expired, ["alice"])


class Regressions(unittest.TestCase):
    """The crash points above that found bugs, reproduced deterministically."""

    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion", 4)
        self.Y = self.net.create_constellation("lyra", 4)
        self.a = Wallet("alice", self.net, self.X, pledge_ttl=TTL, max_skew=SKEW)
        self.b = Wallet("bob", self.net, self.Y, pledge_ttl=TTL, max_skew=SKEW)
        self.x, self.y = self.a.issue("X", 100), self.b.issue("Y", 100)

    def swap_to_kill_switches(self):
        a, b = self.a, self.b
        header, body, _ = propose_swap(a, self.x, 10, b, self.y, 20)
        sig = {s for s, _ in header["inputs"]}
        unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
        for w in (a, b):
            w.cosign(header, unlocks)
        kills = (a.kill_switches | b.kill_switches) & sig
        a.seal(header, body, unlocks, only=sig - kills)
        return header, body, unlocks, kills

    def test_released_kill_switch_keeps_the_pending_swap(self):
        """FINDING (wallet, Medium-High: funds locked for good). A swap's main inputs are sealed;
        alice released her kill switch (pledged it) but the request never reached a witness.
        After expiry ``release_expired_pledges`` releases the unbound kill switch under rule 3,
        and used to drop the whole pending swap with it, although alice's main input stays
        pledged to it and bound: with no pending transition it could never be settled again."""
        a, b = self.a, self.b
        header, body, unlocks, kills = self.swap_to_kill_switches()
        a.authorise(header, body, release_kill=True)     # alice's kill switch pledged, never sent
        # The kill switch settles first (a reload from disk orders pledges by sigil).
        a.pledged = dict(sorted(a.pledged.items(), key=lambda kv: kv[0] not in kills))
        for _ in range(4):
            self.net.clock.advance(TTL + SKEW + 1)
            for w in (a, b):
                w.release_expired_pledges()
        live = {h["sigil"] for h in a.holdings.values()} & set(a.pledged)
        self.assertEqual(live, set(), "alice's main input is stuck pledged to a swap she forgot")

    def test_single_party_seal_stops_at_the_first_failure(self):
        """REVIEW FINDING (Low). A payment of alice's with inputs in two homes, the first home
        down: ``seal`` must not go on binding the healthy home's input to a tid that cannot
        complete now (it did once it bound every input it could, which only swaps need)."""
        a = self.a
        y_kill = a.kill_switch(self.Y)                    # a parcel of alice's homed at Y
        xs = next(h for h in a.holdings.values() if h["parcel"]["home"] == self.X and h["parcel"]["amount"] == 100)
        me = a.address()
        header, body, _ = a.prepare([y_kill["ref"], xs["ref"]],
                                    [model.parcel(self.X, self.x, 100, me["lock"], me["salt"])])
        unlocks = a.authorise(header, body, release_kill=True)
        self.net.down |= {w.pk for w in self.net.all_witnesses(self.Y)}
        with self.assertRaises(SealFailed):
            a.seal(header, body, unlocks)
        self.net.down.clear()
        self.assertTrue(all(w.status(xs["sigil"])["tid"] is None for w in self.net.all_witnesses(self.X)))

    def test_accept_completed_rejects_a_dossier_without_the_transition(self):
        """REVIEW FINDING (Low): a malformed hand-over raised KeyError instead of InvalidDossier."""
        header, body, unlocks, kills = self.swap_to_kill_switches()
        tid = model.transition_id(header)
        from sigil.validate import Dossier
        with self.assertRaises(InvalidDossier):
            self.b.accept_completed(Dossier(), tid)

    def test_swap_settles_when_a_crash_lost_the_counterpartys_unlock(self):
        """FINDING (wallet, Medium-High). Both parties released their kill switches; alice holds
        every unlock (her cosign was saved), bob's crash lost alice's kill-switch unlock (his
        last cosign was not). After expiry alice re-seals: her own kill switch binds with a fresh
        unlock, bob's cannot (her copy of his unlock expired). Bob re-seals: he cannot unlock
        alice's kill switch and used to stop there, before binding his own: neither could ever
        finish (and when both crashed, every input ended up bound with no party able to record
        the swap). Now a party that lacks another's unlock never signs or binds for the
        transition again: its kill switch expires unbound and is spent elsewhere, a death proof
        with which both abort; a party holding every unlock may complete it first and hand it
        over (``Wallet.accept_completed``). ``seal`` also binds every input it can before failing."""
        a, b = self.a, self.b
        header, body, unlocks, kills = self.swap_to_kill_switches()
        tid = model.transition_id(header)
        unlocks.update({**a.authorise(header, body, release_kill=True), **b.authorise(header, body, release_kill=True)})
        a.cosign(header, unlocks)
        a_kill = next(iter(a.kill_switches & kills))
        b.pending[tid]["others"].pop(a_kill, None)      # bob's crash lost it
        for _ in range(4):
            self.net.clock.advance(TTL + SKEW + 1)
            for w in (a, b):
                w.release_expired_pledges()
        if tid in a.dossier.transitions:                # completed: alice hands bob the swap
            b.accept_completed(a.dossier, tid)
        else:                                           # or aborted by both: no one is stuck
            self.assertNotIn(tid, b.dossier.transitions)
        for asset in (self.x, self.y):
            self.assertEqual(a.balance(asset) + b.balance(asset), 100)
        for w in (a, b):
            self.assertEqual({h["sigil"] for h in w.holdings.values()} & set(w.pledged), set())
            for h in w.holdings.values():
                Verifier(TrustPolicy(self.net.registry, {self.X, self.Y})).verify_parcel(w.dossier, h["ref"])


if __name__ == "__main__":
    unittest.main()
