"""Conformance of the REAL wallet against the wallet model (formal/SigilWallet.tla).

WHAT THIS CHECKS
----------------
``formal/SigilWallet.tla`` composes the wallet's state machine with the
witness protocol and TLC checks its invariants exhaustively on small
instances. This test drives the real ``sigil.wallet.Wallet`` (and
``wallet_store`` restarts, ``swap.propose_swap``) under randomised
adversarial schedules and checks, at every step, the same invariants over
the real objects:

* a Byzantine witness in the wallet's home (it votes for anything, lies
  "unbound" in STATUS and claims every release);
* a lossy network: at each step the link to the home is good, lossy or
  partitioned. When lossy, each spend request is delivered, lost but
  delivered LATER (at a random later step, possibly after expiry), or
  delivered with the reply lost, and STATUS and RELEASE can time out; when
  partitioned, every spend request is held back and delivered later;
* wallet crashes in the middle of sealing, and restarts from disk
  (``wallet_store.load``) using the save points of ``sigil.cli cmd_pay``
  (save after authorise, after a failed seal, after finalise);
* the clock jumping forward (expiry), ``release_expired_pledges``, retries
  of failed transitions with the same header, and ``abort`` with death proofs;
* a malicious swap counter-party (Mallory) who cooperates, double-spends her
  own input first, splits her witnesses, or withholds her signature.

REFINEMENT MAPPING (model  <-  code)
-----------------------------------
    pledge          <-  Wallet.pledged[s] = (gen, tid, expires)
    exp[<<g,t>>]    <-  ghost: the latest ``expires`` the wallet ever signed
                        for (s, g, t), read from every unlock ``authorise``
                        returned (it survives restarts: it is the world's view)
    gen, bound      <-  Witness.records[s].gen / .tid of the honest witnesses
    votes           <-  Witness.records[s].votes, plus one forged vote per
                        Byzantine member for anything
    fin             <-  the parcel left ``holdings`` through ``finalise``

INVARIANTS (as in SigilWallet.tla)
---------------------------------
* NoSelfEquiv: whenever the wallet signs (s, g, t), every OTHER tid it ever
  signed at (s, g) is already unsealable: provably dead (a death proof
  exists), or every signature for it has expired and too few witnesses
  voted for it to ever reach a quorum.
* UnpledgeSound/AbortSound: whenever a pledge disappears (dropped, replaced,
  or lost across a restart) the pledged tid is unsealable at that moment,
  and a dropped tid never becomes complete afterwards.
* OneComplete: no parcel of the wallet is consumed by two complete
  transitions; the wallet never finalises two transitions for one parcel.
* PaidIsComplete: every transition the wallet finalised is complete.
* Holdings: every UN-pledged holding is unspent (no complete transition
  consumes its sigil), and verifies from the wallet's own dossier with a
  fresh validator.

What is NOT asserted here, because it is a known bug with its own
``expectedFailure`` test in tests/test_wallet_findings.py: a PLEDGED holding
may have been consumed by a transition the wallet forgot (HeldIsTracked),
and a dead pledge may stay stuck (RecoveryLive). Header-level attacks by the
counter-party (wrong generation, header/body mismatch), poisoned dossiers
and trust policy are likewise only in the targeted tests.

The default run takes a few seconds. Scale with SIGIL_WALLET_SEEDS and
SIGIL_WALLET_STEPS.
"""

import os
import random
import tempfile
import unittest
from unittest import mock

from sigil import Network, SealFailed, Wallet
from sigil import model, wallet_store
from sigil.charter import quorum
from sigil.swap import propose_swap
from sigil.validate import InvalidDossier, TrustPolicy, Verifier
from sigil.wallet import request_seal
from sigil.witness import Rejected
from tests.adversary import Equivocator
from tests.test_security import manual_spend

SEEDS = int(os.environ.get("SIGIL_WALLET_SEEDS", "12"))
STEPS = int(os.environ.get("SIGIL_WALLET_STEPS", "40"))


class Crash(Exception):
    """The wallet process dies."""


class ModelViolation(AssertionError):
    """The real wallet left a state the wallet model forbids."""


class ByzX(Equivocator):
    """Votes for anything; reports every sigil unbound; claims every release."""

    def status(self, sigil):
        return {"gen": 0, "tid": None, "votes": []}

    def release(self, sigil, proof):
        return 1


class Proxy:
    """A lossy link to one witness of the wallet's home."""

    def __init__(self, u: "Universe", w):
        self.u, self.w, self.pk, self.stamps = u, w, w.pk, None

    def spend(self, req):
        u, r = self.u, self.u.rng.random()
        if u.mode == "partition":
            u.delayed.append((self.w, req))
            raise Rejected("unreachable")
        if u.crash_armed and r < 0.04:
            if u.rng.random() < 0.5:
                try:
                    self.w.spend(req)
                except Rejected:
                    pass
            raise Crash
        if u.mode == "good":
            return self.w.spend(req)
        if r < 0.25:
            u.delayed.append((self.w, req))     # lost now, delivered later
            raise Rejected("timeout")
        if r < 0.45:
            try:
                self.w.spend(req)                # delivered, reply lost
            except Rejected:
                pass
            raise Rejected("timeout")
        return self.w.spend(req)

    def status(self, sigil):
        if self.u.mode != "good" and self.u.rng.random() < 0.2:
            raise Rejected("timeout")
        return self.w.status(sigil)

    def release(self, sigil, proof):
        if self.u.mode != "good" and self.u.rng.random() < 0.2:
            raise Rejected("timeout")
        return self.w.release(sigil, proof)


class FlakyNetwork(Network):
    """Witnesses of ``self.flaky`` are reached through lossy proxies."""

    flaky: str | None = None
    universe: "Universe | None" = None

    def _wrap(self, cid, ws):
        if cid != self.flaky:
            return ws
        return [Proxy(self.universe, w) for w in ws]

    def witnesses(self, cid):
        return self._wrap(cid, super().witnesses(cid))

    def all_witnesses(self, cid):
        return self._wrap(cid, super().all_witnesses(cid))

    def find_votes(self, sigil):
        out = []
        for cid in self.members:
            for w in self.witnesses(cid):
                try:
                    out.extend(w.status(sigil)["votes"])
                except Rejected:
                    pass
        return out


class Universe:
    def __init__(self, rng: random.Random, path: str):
        self.rng, self.path = rng, path
        self.net = FlakyNetwork()
        self.net.universe = self
        self.X = self.net.create_constellation("home", 4, byzantine={3: ByzX})
        self.Y = self.net.create_constellation("lyra", 4)
        self.net.flaky = self.X
        self.honest = {self.X: self.net.members[self.X][:3], self.Y: self.net.members[self.Y]}
        self.byz = {self.X: 1, self.Y: 0}
        self.crash_armed = False
        self.mode = "good"                    # link quality to the home: good | lossy | partition
        self.delayed: list = []
        self.alice = Wallet("alice", self.net, self.X)
        self.usd = self.alice.issue("USD", 1_000)
        self.sinks = [Wallet(f"sink{i}", self.net, self.X) for i in range(2)]
        self.mallory = Wallet("mallory", self.net, self.Y)
        self.save()
        # ghost state
        self.signed: dict[tuple, dict] = {}   # (s, g) -> {tid: max expires}
        self.headers: dict[str, dict] = {}    # tid -> header (every tid alice signed)
        self.homes: dict[str, str] = {}       # sigil -> home
        self.mine: set[str] = set()           # alice's sigils
        self.dropped: set[tuple] = set()      # (s, g, t)
        self.finalised: dict[str, str] = {}   # parcel id -> tid
        self.failed: dict[str, tuple] = {}    # tid -> (header, body, extra unlocks)
        self.tracked: set[tuple] = set()      # every (s, g, t) pledge seen since the last drop check

    # ------------------------------------------------------------ the world

    def save(self):
        wallet_store.save(self.alice, self.path)

    def restart(self):
        self.track()
        self.alice = wallet_store.load(self.path, self.net)
        self.check_drops()

    def track(self):
        self.tracked |= {(s, p[0], p[1]) for s, p in self.alice.pledged.items()}

    def votes(self, s, g):
        out: dict[str, set] = {}
        for w in self.honest[self.homes.get(s, self.X)]:
            rec = w.records.get(s)
            for v in (rec.votes if rec else []):
                if v["gen"] == g:
                    out.setdefault(v["tid"], set()).add(v["witness"])
        return out

    def q(self, s):
        return quorum(4)

    def sealed(self, s, g, t):
        return len(self.votes(s, g).get(t, ())) + self.byz[self.homes.get(s, self.X)] >= self.q(s)

    def dead(self, t):
        for s, g in self.headers[t]["inputs"]:
            vs = self.votes(s, g)
            if any(u != t and self.sealed(s, g, u) for u in vs):
                return True
            against = set().union(*[ws for u, ws in vs.items() if u != t]) if vs else set()
            if len(against) + self.byz[self.homes.get(s, self.X)] >= self.q(s):
                return True
        return False

    def complete(self, t):
        return all(self.sealed(s, g, t) for s, g in self.headers[t]["inputs"])

    def unsealable(self, s, g, t):
        if self.dead(t):
            return True
        exp = self.signed.get((s, g), {}).get(t)
        expired = exp is not None and self.net.clock() > exp
        few = len(self.votes(s, g).get(t, ())) + self.byz[self.homes.get(s, self.X)] < self.q(s)
        return expired and few

    # -------------------------------------------------------- the wallet ops

    def sign(self, header, body):
        """Wallet.authorise, with the NoSelfEquiv check at signing time."""
        tid = model.transition_id(header)
        for r, (s, _g) in zip(body["inputs"], header["inputs"]):
            try:
                self.homes[s] = self.alice.dossier.output(r)["home"]
            except InvalidDossier:
                pass
        self.track()
        unlocks = self.alice.authorise(header, body)
        self.headers[tid] = header
        self.track()   # pledges made here and dropped later in this op are checked too
        for s, g in header["inputs"]:
            if s not in unlocks:
                continue
            self.mine.add(s)
            for other in self.signed.get((s, g), {}):
                if other != tid and not self.unsealable(s, g, other):
                    raise ModelViolation(f"NoSelfEquiv: signed {tid[:8]} at ({s[:8]},{g}) "
                                         f"while {other[:8]} can still be sealed")
            d = self.signed.setdefault((s, g), {})
            d[tid] = max(d.get(tid, unlocks[s]["expires"]), unlocks[s]["expires"])
        return unlocks

    def seal_and_finalise(self, header, body, unlocks, extra=None):
        """cmd_pay after the pledge is saved: seal, unpledge on failure, finalise."""
        tid = model.transition_id(header)
        self.crash_armed = True
        try:
            self.alice.seal(header, body, {**(extra or {}), **unlocks})
        except SealFailed:
            self.crash_armed = False
            for s, _ in header["inputs"]:
                self.alice.unpledge_if_unbound(s)
            self.save()
            self.failed[tid] = (header, body, extra or {})
            return None
        except Crash:
            self.crash_armed = False
            self.failed[tid] = (header, body, extra or {})
            self.restart()
            return None
        self.crash_armed = False
        if not self.complete(tid):
            raise ModelViolation(f"PaidIsComplete: wallet sealed {tid[:8]} but it is not complete")
        for r in body["inputs"]:
            pid = model.parcel_id(r)
            if pid in self.alice.holdings:
                if pid in self.finalised and self.finalised[pid] != tid:
                    raise ModelViolation("the wallet finalised two transitions for one parcel")
                self.finalised[pid] = tid
        self.alice.finalise(header, body, {**(extra or {}), **unlocks})
        self.save()
        self.failed.pop(tid, None)
        return tid

    def op_pay(self):
        to = self.rng.choice(self.sinks)
        amount = self.rng.choice([1, 5, 20, 100])
        try:
            refs, outs = self.alice.payment_outputs(self.usd, amount, to.address())
        except ValueError:
            return
        header, body, _ = self.alice.prepare(refs, outs)
        unlocks = self.sign(header, body)
        self.save()                                  # persist the pledge first
        tid = self.seal_and_finalise(header, body, unlocks)
        if tid is not None:
            to.receive(self.alice.dossier.ancestry([tid]), [model.ref(tid, 0)])

    def op_swap(self):
        m = self.mallory
        gold = m.issue("GOLD", 10)
        try:
            header, body, _ = propose_swap(self.alice, self.usd, self.rng.choice([1, 10]), m, gold, 10)
        except ValueError:
            return
        mode = self.rng.choice(["coop", "coop", "betray", "split", "withhold"])
        unlocks = self.sign(header, body)
        self.save()
        um = {} if mode == "withhold" else m.authorise(header, body)
        mref = body["inputs"][-1]
        me = m.address()
        out = [model.parcel(self.Y, gold, 10, me["lock"], me["salt"])]
        if mode == "betray":
            request_seal(self.net, manual_spend(m, [mref], out, memo="betray")[3][0])
        elif mode == "split":
            r1 = manual_spend(m, [mref], out, memo="a")[3][0]
            r2 = manual_spend(m, [mref], out, memo="b")[3][0]
            ws = self.net.witnesses(self.Y)
            for w, r in zip(ws, [r1, r1, r2, r2]):
                try:
                    w.spend(r)
                except Rejected:
                    pass
        for s, g in header["inputs"]:
            self.homes.setdefault(s, self.Y)
        self.seal_and_finalise(header, body, unlocks, um)

    def op_retry(self):
        if not self.failed:
            return
        tid = self.rng.choice(sorted(self.failed))
        header, body, extra = self.failed[tid]
        # Re-authorising a header whose generation for one of our inputs is no
        # longer the holding's (e.g. after an abort moved it on) makes the real
        # wallet overwrite a live pledge: that is the authorise generation bug
        # (tests/test_wallet_findings.py, AuthoriseTests), which this run found
        # on its own. A careful application does not retry such a header, so
        # neither do we here.
        held = {model.parcel_id(h["ref"]): h for h in self.alice.holdings.values()}
        for r, (_s, g) in zip(body["inputs"], header["inputs"]):
            h = held.get(model.parcel_id(r))
            if h is not None and h["gen"] != g:
                return
        try:
            unlocks = self.sign(header, body)
        except ValueError:
            return
        self.save()
        self.seal_and_finalise(header, body, unlocks, extra)

    def op_abort(self):
        if not self.failed:
            return
        tid = self.rng.choice(sorted(self.failed))
        try:
            self.alice.abort(self.failed[tid][0])
        except ValueError:
            pass
        self.save()

    def op_deliver(self):
        if not self.delayed:
            return
        w, req = self.delayed.pop(self.rng.randrange(len(self.delayed)))
        try:
            w.spend(req)
        except Rejected:
            pass

    def op_receive(self):
        src = self.rng.choice(self.sinks)
        if src.balance(self.usd) < 5:
            return
        try:
            src.pay(self.alice, self.usd, 5)
        except (SealFailed, ValueError):
            return
        self.save()

    def step(self):
        self.track()
        self.mode = self.rng.choices(["good", "lossy", "partition"], [0.5, 0.35, 0.15])[0]
        r = self.rng.random()
        if r < 0.25:
            self.op_pay()
        elif r < 0.40:
            self.op_swap()
        elif r < 0.55:
            self.op_deliver()
        elif r < 0.65:
            self.net.clock.advance(self.rng.choice([30, 300, 700, 1000]))
        elif r < 0.72:
            self.alice.release_expired_pledges()
            self.save()
        elif r < 0.80:
            self.op_retry()
        elif r < 0.86:
            self.op_abort()
        elif r < 0.92:
            self.op_receive()
        else:
            self.restart()
        self.check_drops()
        self.check_state()

    # ------------------------------------------------------------- checks

    def check_drops(self):
        now = self.alice.pledged
        before = self.tracked
        self.tracked = {(s, p[0], p[1]) for s, p in now.items()}
        for s, g, t in before:
            cur = now.get(s)
            if cur is not None and tuple(cur[:2]) == (g, t):
                continue
            if not self.unsealable(s, g, t):
                raise ModelViolation(f"UnpledgeSound: dropped the pledge ({s[:8]},{g},{t[:8]}) "
                                     "while it could still be sealed")
            self.dropped.add((s, g, t))

    def check_state(self):
        for s, g, t in self.dropped:
            if self.complete(t) and t not in self.finalised.values():
                raise ModelViolation(f"a dropped pledge {t[:8]} completed later")
        for s in self.mine:
            done = {t for t, h in self.headers.items() if any(x == s for x, _ in h["inputs"]) and self.complete(t)}
            if len(done) > 1:
                raise ModelViolation(f"OneComplete: {s[:8]} consumed by {len(done)} complete transitions")
        verifier = Verifier(TrustPolicy(self.net.registry))
        for pid, h in self.alice.holdings.items():
            s = h["sigil"]
            if s in self.alice.pledged:
                continue  # in flight; see tests/test_wallet_findings.py for what can go wrong
            for t, hd in self.headers.items():
                if any(x == s for x, _ in hd["inputs"]) and self.complete(t):
                    raise ModelViolation(f"holding {s[:8]} is not pledged but consumed by {t[:8]}")
            try:
                verifier.verify_parcel(self.alice.dossier, h["ref"])
            except InvalidDossier as e:
                raise ModelViolation(f"holding {s[:8]} does not verify from the wallet's dossier: {e}")


class WalletConformanceTests(unittest.TestCase):
    def run_seeds(self, seeds, steps):
        stats = {"pays": 0, "drops": 0, "finalised": 0}
        for seed in range(seeds):
            with tempfile.TemporaryDirectory() as d:
                u = Universe(random.Random(seed), os.path.join(d, "alice"))
                for _ in range(steps):
                    u.step()
                stats["drops"] += len(u.dropped)
                stats["finalised"] += len(set(u.finalised.values()))
        return stats

    def test_real_wallet_satisfies_the_wallet_model(self):
        """The real Wallet never violates the SigilWallet.tla safety invariants
        under lossy links, delayed requests, crashes, a Byzantine witness and a
        malicious swap counter-party -- and the runs are not vacuous."""
        stats = self.run_seeds(SEEDS, STEPS)
        self.assertGreater(stats["finalised"], 0, "no payment ever completed: the run is vacuous")
        self.assertGreater(stats["drops"], 0, "no pledge was ever dropped: the run is vacuous")

    def _caught(self, patches) -> bool:
        with patches:
            try:
                self.run_seeds(SEEDS, STEPS)
            except ModelViolation:
                return True
        return False

    def test_detects_unpledge_without_expiry(self):
        """Mutation: unpledge ignores the expiry (max_skew = -inf). Must be caught."""
        real = Wallet.unpledge_if_unbound

        def eager(self, sigil):
            self.max_skew = -10 ** 12
            return real(self, sigil)
        self.assertTrue(self._caught(mock.patch.object(Wallet, "unpledge_if_unbound", eager)),
                        "the checks missed a wallet that drops unexpired pledges")

    def test_detects_a_wallet_that_forgets_its_pledges(self):
        """Mutation: authorise ignores earlier pledges (no equivocation guard). Must be caught."""
        real = Wallet.authorise

        def forgetful(self, header, body, extra=None):
            self.pledged.clear()
            return real(self, header, body, extra)
        self.assertTrue(self._caught(mock.patch.object(Wallet, "authorise", forgetful)),
                        "the checks missed a wallet that signs two spends of one sigil")


if __name__ == "__main__":
    unittest.main()
