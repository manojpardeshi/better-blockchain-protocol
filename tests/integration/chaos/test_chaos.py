"""Fault-injection (chaos) integration tests: real Rust and Python witness processes over HTTP.

    python -m unittest discover -s tests/integration -t .        # fast default, a few minutes
    SIGIL_CHAOS_SEEDS=1-40 SIGIL_CHAOS_OPS=60 python -m unittest tests.integration.chaos.test_chaos
    python -m tests.integration.chaos.run --minutes 60 --out stats.json   # long runs with statistics

Skipped when the Rust witness binary (``rust/target/release/sigil-witness``, or
``$SIGIL_WITNESS_BIN``) is missing. See ``run.py`` for the harness and ``invariants.py``
for what is checked.

* ``SeededChaos`` runs whole randomized constellations under every fault type and asserts
  the global safety invariants, and liveness once the faults heal.
* ``Scenarios`` drive one fault at a time deterministically (delayed request past expiry,
  disk full, partition longer than ``dead_man``, Byzantine witnesses within *f*).
* ``NonVacuity`` shows the checks have teeth: a witness that votes without persisting, one
  that skips the expiry check, Byzantine witnesses beyond *f* and clocks beyond the skew
  bound must each be reported as violations.
* ``Findings`` are product bugs found by the harness, as ``expectedFailure`` tests: a
  malformed STATUS from one Byzantine witness crashes honest wallets; a pledge released under
  rule 3 is resurrected (and can be completed) after a succession; an atomic swap interrupted
  after its kill switches were released can never be finished or aborted; a failed succession
  attempt fences standby members and halts a live home. The seeded runs report the last three
  as ``known:`` liveness entries instead of failing.

Environment: ``SIGIL_CHAOS_SEEDS`` (default 101,102,103), ``SIGIL_CHAOS_OPS`` (18),
``SIGIL_CHAOS_STRICT_LIVENESS`` (1), ``SIGIL_CHAOS_VERBOSE``, ``SIGIL_CHAOS_TRACE`` (Python
witnesses log the traceback behind every HTTP 500), ``SIGIL_CHAOS_KEEP_FAILED`` (keep the
directories of failed runs), ``SIGIL_CHAOS_RUST_MUTANTS=1`` (build and check mutated Rust
witnesses).
"""

import os
import random
import threading
import time
import unittest

from sigil import model
from sigil.charter import Registry
from sigil.server import RemoteStandby, RemoteWitness
from sigil.wallet import SealFailed, request_seal
from sigil.witness import Rejected

from . import invariants
from .run import ChaosRun, Config, _seeds, rust_available

QUIET = os.environ.get("SIGIL_CHAOS_VERBOSE") != "1"


def _log(line):
    if not QUIET:
        print(line, flush=True)


def kinds_of(violations) -> set:
    return {v["kind"] for v in violations}


@unittest.skipUnless(rust_available(), "Rust witness binary missing: cargo build --release --locked in rust/")
class ChaosCase(unittest.TestCase):
    """A ``ChaosRun`` set up without its chaos thread, driven step by step by the test."""

    def scenario(self, seed: int = 1000, **over) -> ChaosRun:
        base = dict(sizes=[4, 4], committee=False, rotation=False, succession=False, kills=False, hooks=False,
                    net_faults=False, partitions=False, skew="none", disk=False, byz=0, byz_other=0,
                    mallory=False, delayed_expiry=0, workers=1, ops=0)
        base.update(over)
        cfg = Config(seed=seed, **base)
        run = ChaosRun(cfg, log=_log)
        self.addCleanup(run.finish)
        run.setup()
        return run

    def check(self, run: ChaosRun, *, clock_assumption: bool = True) -> list:
        """Heal, then every global invariant; ``clock_assumption=False`` also holds witnesses
        whose clock left the skew bound to S6."""
        run.heal()
        if not clock_assumption:
            run.faulty_clock.clear()
        run.check()
        return run.violations

    def pay(self, run: ChaosRun, a: str, b: str, amount: int = 5) -> str:
        payer, payee = run.wallets[a], run.wallets[b]
        asset = next(x for x in run.assets if payer.balance(x) >= amount)
        refs, outputs = payer.payment_outputs(asset, amount, payee.address())
        tid = run._transact(payer, refs, outputs, payee)
        self.assertTrue(run._deliver(payer, payee, tid, [model.ref(tid, 0)]))
        return tid


    def pay_eventually(self, run: ChaosRun, a: str, b: str, amount: int, within: float = 40) -> str:
        """Pay once pledges left by faults have settled (expiry + skew), within ``within`` s."""
        deadline, err = time.monotonic() + within, None
        while time.monotonic() < deadline:
            with run._locked(a, b):
                run.wallets[a].release_expired_pledges()
                try:
                    return self.pay(run, a, b, amount)
                except (ValueError, SealFailed) as e:
                    err = e
            time.sleep(1)
        self.fail(f"{a} could not pay {b} within {within}s: {err!r}")


class SeededChaos(ChaosCase):
    """Randomized runs: every fault type, Rust and Python mixed, safety always, liveness after healing."""

    def test_seeded_runs(self):
        seeds = _seeds(os.environ.get("SIGIL_CHAOS_SEEDS", "101,102,103"))
        ops = int(os.environ.get("SIGIL_CHAOS_OPS", "18"))
        strict = os.environ.get("SIGIL_CHAOS_STRICT_LIVENESS", "1") == "1"
        for seed in seeds:
            with self.subTest(seed=seed):
                # Malformed replies from a Byzantine witness crash wallets (Findings), which
                # leaves pledges no settle can finish; they get their own runs and test.
                cfg = Config.random(seed, ops=ops, byz_modes="equivocate,lie,withhold")
                res = ChaosRun(cfg, log=_log).run()
                self.assertEqual(res["violations"], [], f"seed {seed}: safety violated: {res['violations']}")
                self.assertEqual([a["key"] for a in res["anomalies"]], [], f"seed {seed}: {res['anomalies']}")
                if strict:
                    # "known:" entries are open findings with their own expectedFailure tests
                    unknown = [x for x in res["liveness"] if not x["kind"].startswith("known:")]
                    self.assertEqual(unknown, [], f"seed {seed}: no liveness after healing")


class Scenarios(ChaosCase):
    def test_request_delivered_after_expiry_is_refused(self):
        """SPEC §4 rule 3 / §5.1 step 4 over real processes: the payment is held in flight,
        the wallet releases its pledge after expiry + skew and pays someone else, and the held
        requests, delivered right after the release, bind nothing (Rust and Python)."""
        run = self.scenario(kinds="mixed")
        self.assertEqual(run.delayed_expiry("alice", "bob", "carol", random.Random(1)), "ok")
        self.assertGreater(run.faults["delivered-after-expiry"], 0)
        self.assertEqual(self.check(run), [])
        self.assertTrue(run.released)

    def test_clock_shim_skews_both_implementations(self):
        """Harness self-check: the LD_PRELOAD clock shim moves the wall clock of a running Rust
        and a running Python witness (their vote ``time``), so the skew faults are real."""
        run = self.scenario(kinds="mixed", skew="within")
        if run.skew_so is None:
            self.skipTest("no C compiler for the clock shim")
        c, home = run.c, run.cids[0]
        picks = {k: next(j for j in c.indices(home) if c.witnesses[j]["kind"] == k) for k in ("rust", "python")}
        for i in picks.values():
            c.set_skew(i, -5000)   # behind: fresh authorisations still look unexpired
        time.sleep(0.2)
        self.pay(run, "alice", "bob", 1)
        now = time.time()
        for kind, i in picks.items():
            times = [v["time"] for k, v in run.obs.votes.items() if k[0] == c.witnesses[i]["pk"]]
            self.assertTrue(times and min(times) < now - 4000, f"{kind} witness clock not skewed: {times}")
            c.set_skew(i, 0)
        run.faulty_clock.clear()

    def test_disk_full_witness_refuses_rather_than_votes_unpersisted(self):
        """A full disk on a witness (Python: the store cannot grow; Rust: likewise, which the Rust
        store answers by aborting): payments still seal from the others, the witness emits no
        vote it did not persist (checked after a SIGKILL and restart by S5), and it serves again
        once the disk has room."""
        run = self.scenario(kinds="mixed", disk=True)
        c = run.c
        home = run.cids[0]
        for kind in ("python", "rust"):
            with self.subTest(kind=kind):
                i = next(j for j in c.indices(home) if c.witnesses[j]["kind"] == kind)
                name = c.proxies[i].name
                before = set(run.obs.emitted[name])
                how = c.fill_disk(i)
                if how is None:
                    self.skipTest("neither a tmpfs nor RLIMIT_FSIZE is available")
                for _ in range(3):
                    self.pay(run, "alice", "bob", 3)
                full = run.obs.emitted[name] - before
                # anything it did emit while full must be durable: SIGKILL, free, restart, S5
                c.kill(i)
                c.free_disk(i)
                self.assertTrue(c.restart(i))
                st = RemoteWitness(c.real_url(i)).status
                for k in full:
                    votes = st(k[3])["votes"]
                    self.assertIn(k, {invariants._vote_key(v) for v in votes}, f"{how}: vote not persisted")
                before = set(run.obs.emitted[name])
                self.pay(run, "alice", "bob", 3)
                self.assertTrue(run.obs.emitted[name] - before, f"{kind} witness serves again after the disk is freed")
        self.assertEqual(self.check(run), [])

    def test_partition_longer_than_dead_man_succeeds_safely(self):
        """The home's members are cut off from their successor committee (heartbeat probes
        refused) for longer than ``dead_man`` while wallets keep paying through them; the
        committee signs a succession, the new members adopt, the old version (still running)
        can no longer seal, and nothing is consumed twice."""
        run = self.scenario(kinds="mixed", committee=True, dead_man=3)
        stop = threading.Event()
        paid = []

        def payer():
            while not stop.is_set():
                try:
                    with run._locked("alice", "bob"):
                        paid.append(self.pay(run, "alice", "bob", 1))
                except (SealFailed, ValueError, Rejected):
                    pass
                time.sleep(0.2)

        old = list(run.directory[run.cids[0]])
        old_k = list(run.committees[run.cids[0]])
        t = threading.Thread(target=payer)
        t.start()
        try:
            outcome = run.op_succession(random.Random(7))
        finally:
            stop.set()
            t.join()
        self.assertEqual(outcome, "ok")
        self.assertGreater(len(paid), 0)
        self.assertTrue(all(RemoteStandby(u).info()["fenced"] for u in old_k))
        self.pay_eventually(run, "alice", "bob", 1)   # the successor serves (once in-flight pledges settled)
        # the old version is alive but can no longer seal anything new
        stale = run.mallory.network
        stale.urls[run.cids[0]], stale.committees[run.cids[0]] = old, old_k
        stale._clients.clear()
        stale._standbys.clear()
        coin = next(h for h in run.mallory.holdings.values() if h["parcel"]["asset"] == run.mal_asset)
        a = run.mallory.address()
        header, body, tid = run.mallory.prepare([coin["ref"]], [model.parcel(a["home"], run.mal_asset,
                                                coin["parcel"]["amount"], a["lock"], a["salt"])])
        unlocks = run.mallory.authorise(header, body)
        p = coin["parcel"]
        req = {"sigil": coin["sigil"], "header": header, "home": p["home"], "lock": p["lock"], "salt": p["salt"],
               "unlock": unlocks[coin["sigil"]]}
        with self.assertRaises(SealFailed):
            request_seal(stale, req)
        self.assertEqual(self.check(run), [])

    def test_byzantine_within_f_equivocating_owner(self):
        """One Byzantine witness of four (equivocates, lies on STATUS, withholds gossip) colludes
        with an owner who signs two transitions of one coin and splits the honest witnesses
        between them: at most one is ever sealed."""
        run = self.scenario(kinds="mixed", byz=1, byz_modes="equivocate,lie,withhold,always", mallory=True,
                            mallory_targeted=1.0)
        outcomes = [run.op_mallory(random.Random(k)) for k in range(4)]
        self.assertNotIn("sealed-2", outcomes)
        self.assertEqual(self.check(run), [])


class NonVacuity(ChaosCase):
    """Broken witnesses and broken assumptions must be reported: the checks have teeth."""

    def test_mutant_voting_without_persisting_is_caught(self):
        """A Python witness whose records never reach its store (``mutant.py nopersist``):
        after a SIGKILL and restart it has forgotten its votes (S5) and, asked again, signs a
        second transaction for the same (sigil, gen) (S2), so a second seal forms (S1b)."""
        run = self.scenario(kinds="python", mutant="nopersist", mallory=True, mallory_targeted=0.0)
        self.pay(run, "alice", "bob")
        self._equivocate_across_restart(run)
        found = kinds_of(self.check(run))
        self.assertIn("S5-vote-forgotten", found)
        self.assertIn("S2-honest-equivocation", found)

    def test_control_honest_witnesses_survive_the_same_crash(self):
        """The same schedule against honest Rust and Python witnesses: nothing to report."""
        run = self.scenario(kinds="mixed", mallory=True, mallory_targeted=0.0)
        self.pay(run, "alice", "bob")
        self._equivocate_across_restart(run)
        self.assertEqual(self.check(run), [])

    def _equivocate_across_restart(self, run):
        """mallory gets T1 sealed, every home witness is SIGKILLed and restarted, then T2."""
        m, c = run.mallory, run.c
        coin = next(h for h in m.holdings.values() if h["parcel"]["asset"] == run.mal_asset)
        reqs = []
        for k in range(2):
            a = m.address()
            header, body, tid = m.prepare([coin["ref"]], [model.parcel(a["home"], run.mal_asset,
                                          coin["parcel"]["amount"], a["lock"], a["salt"])], memo=f"t{k}")
            from sigil import locks
            exp = int(time.time()) + 60
            u = locks.empty_unlock(exp)
            for pk in locks.keys_in(coin["parcel"]["lock"]) & set(m.keys):
                u["sigs"][pk] = locks.sign_unlock(m.keys[pk], coin["sigil"], tid, exp)
            p = coin["parcel"]
            reqs.append({"sigil": coin["sigil"], "header": header, "home": p["home"], "lock": p["lock"],
                         "salt": p["salt"], "unlock": u})
        request_seal(m.network, reqs[0])
        for i in c.indices(run.cids[0]):
            c.kill(i)
        for i in c.indices(run.cids[0]):
            self.assertTrue(c.restart(i))
        m.network._clients.clear()
        try:
            request_seal(m.network, reqs[1])
        except SealFailed:
            pass

    def test_mutant_skipping_the_expiry_check_is_caught(self):
        """Witnesses that newly bind on an expired authorisation (``mutant.py noexpiry``): the
        held payment, delivered after the wallet released its pledge, gets votes (S6)."""
        run = self.scenario(kinds="python", mutant="noexpiry")
        try:
            run.delayed_expiry("alice", "bob", "carol", random.Random(1))
        except (ValueError, SealFailed):
            pass  # the late binding makes the wallet refuse the second payment (or it fails)
        self.assertIn("S6-vote-after-pledge-release", kinds_of(self.check(run)))

    @unittest.skipUnless(os.environ.get("SIGIL_CHAOS_RUST_MUTANTS") == "1",
                         "builds mutated Rust witnesses (minutes): set SIGIL_CHAOS_RUST_MUTANTS=1")
    def test_rust_mutants_are_caught(self):
        """The same two mutations in the Rust witness (``rust_mutants.py``): a build whose
        records never reach redb, and one that binds on expired authorisations."""
        from . import rust_mutants
        from .cluster import RUST_MUTANT_BINS
        work = os.environ.get("SIGIL_CHAOS_MUTANT_DIR") or os.path.join(
            os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))),
            "rust", "target", "chaos-mutants")
        os.makedirs(work, exist_ok=True)
        for name in ("nopersist", "noexpiry"):
            RUST_MUTANT_BINS[name] = rust_mutants.build(name, work)
        with self.subTest("nopersist"):
            run = self.scenario(mutant="rust:nopersist", mallory=True, mallory_targeted=0.0)
            self.pay(run, "alice", "bob")
            self._equivocate_across_restart(run)
            found = kinds_of(self.check(run))
            self.assertIn("S5-vote-forgotten", found)
            self.assertIn("S2-honest-equivocation", found)
        with self.subTest("noexpiry"):
            run = self.scenario(mutant="rust:noexpiry")
            try:
                run.delayed_expiry("alice", "bob", "carol", random.Random(1))
            except (ValueError, SealFailed):
                pass
            self.assertIn("S6-vote-after-pledge-release", kinds_of(self.check(run)))

    def test_byzantine_beyond_f_is_caught(self):
        """Two Byzantine witnesses of four (f = 1) with an equivocating owner: both
        transitions of one coin are sealed, and the harness reports the double consumption."""
        run = self.scenario(kinds="mixed", byz=2, byz_modes="equivocate,always", mallory=True,
                            mallory_targeted=1.0)
        outcomes = [run.op_mallory(random.Random(k)) for k in range(2)]
        self.assertIn("sealed-2", outcomes)
        found = kinds_of(self.check(run))
        self.assertIn("S1-double-consumption", found)
        self.assertIn("S1b-two-seals-one-generation", found)

    def test_clock_skew_beyond_bound_is_caught(self):
        """Every witness of the home lags the wallet by more than ``max_skew``: the held
        payment binds after the wallet released its pledge. Within the assumption the harness
        treats these witnesses as faulty (S6 skips them); held to S6 they are reported."""
        run = self.scenario(kinds="mixed", skew="beyond_q")
        if run.skew_so is None:
            self.skipTest("no C compiler for the clock shim")
        try:
            run.delayed_expiry("alice", "bob", "carol", random.Random(1))
        except (ValueError, SealFailed):
            pass  # the late binding makes the wallet refuse the second payment (or it fails)
        self.assertIn("S6-vote-after-pledge-release", kinds_of(self.check(run, clock_assumption=False)))


class Findings(ChaosCase):
    """Product bugs the chaos harness found. Each asserts the property that should hold."""

    @unittest.expectedFailure
    def test_byzantine_malformed_status_crashes_honest_wallets(self):
        """FINDING (Medium, liveness / robustness; found by seeds 2 and 3 of
        ``python -m tests.integration.chaos.run --seeds 2-4``, reproduced here deterministically).

        Scenario: constellation of 4 (f = 1) with one Byzantine witness that answers STATUS
        with a well-formed HTTP 200 whose ``ok`` value is malformed (a list, a string, a
        status whose ``votes`` holds non-objects or votes without ``gen``). An honest wallet
        then pays, receives and recovers through ``Wallet._bound_elsewhere``,
        ``Wallet.receive``, ``Wallet.unpledge_if_unbound`` and ``find_death_proof``, which
        index the reply without validating it (``st["gen"]``, ``v["gen"]``,
        ``(...).get("tid")``) and raise ``TypeError`` / ``KeyError`` / ``AttributeError`` --
        exception types none of the callers catch (they only catch ``Rejected``).

        Impact: one Byzantine witness, within the fault bound, stops every honest holder of
        its constellation from paying (``authorise`` raises before anything is sent), from
        accepting payments (``receive`` raises) and from settling expired pledges
        (``release_expired_pledges`` raises, so pledges are never released and coins stay
        locked). Safety holds; liveness within f does not, contrary to docs/WIRE.md "Nothing
        a witness sends is trusted".

        Suggested fix: validate replies at the client boundary: ``RemoteWitness.status``
        (and ``spend``'s vote, ``info``) should check the shape (``gen`` an int, ``tid`` a
        str or null, ``votes`` a list of objects) and raise ``Unreachable``/``Rejected`` on
        anything else, and the wallet helpers should skip votes that are not objects with
        the expected keys (``verify_vote`` first, then index).
        """
        run = self.scenario(kinds="mixed", byz=1, byz_modes="badstatus,always")
        errors = []
        for k in range(4):
            try:
                with run._locked("alice", "bob"):
                    self.pay(run, "alice", "bob", 1)
            except (SealFailed, ValueError, Rejected):
                pass
            except Exception as e:  # noqa: BLE001
                errors.append(repr(e))
        self.assertEqual(errors, [], "a malformed STATUS from one Byzantine witness crashed an honest wallet")

    @unittest.expectedFailure
    def test_released_pledge_resurrected_by_succession(self):
        """FINDING (Medium, liveness / owner intent; SPEC §4 rule 3 vs §5.5; found while
        analysing delayed-request + succession interleavings of the seeded runs, reproduced
        here deterministically).

        Scenario: home with a successor committee. alice pays bob (T1): the committee mirrors
        T1 and acknowledges, but every SPEND to the home's witnesses is lost in flight (held
        by the network). T1 expires; ``release_expired_pledges`` asks every *witness* for
        STATUS, none holds a binding, so the pledge is released (rule 3), exactly as
        specified. Then the home is cut off from its committee for longer than ``dead_man``
        and the committee succeeds it: the new members ADOPT the committee's mirror logs,
        in which T1's bind entry is the only (hence "lone alive", SPEC §5.4) binding of the
        coin, so every new member is now *bound to T1*.

        Impact: alice's coin is stranded: ``authorise`` of any other spend refuses
        ("already bound to another transition"), no death proof for T1 can exist (nothing
        else is bound at that generation), and the wallet forgot T1 when it released the
        pledge, so it never completes it. Anyone holding the lost T1 request (the network
        adversary that delayed it) can also complete T1 later: the committee re-acks a
        binding it holds and the new members vote a binding they hold whatever the expiry,
        so a payment its owner considered cancelled goes through. Safety holds (a second
        spend of the coin at that generation is impossible), but rule 3's promise "no
        delayed request can still bind it" does not survive a succession.

        Suggested fix: make rule 3 consult the committee too (a pledge is released only if
        every standby member of the current committee also answered and holds no bind
        entry for it, or holds a release for it), or have ``unpledge_if_unbound`` file a
        ``note_release``-like "expired, never voted" entry that ADOPT treats as dead; and
        state in SPEC §5.4/§5.5 how an expired, never-voted mirrored binding is handled.
        """
        run = self.scenario(kinds="mixed", committee=True, dead_man=3)
        alice, bob = run.wallets["alice"], run.wallets["bob"]
        cid = run.cids[0]
        asset = next(a for a in run.assets if alice.balance(a) > 0)
        refs, outputs = alice.payment_outputs(asset, 5, bob.address())
        sigil = alice.holdings[model.parcel_id(refs[0])]["sigil"]
        witnesses = [run.c.proxies[i] for i in run.c.indices(cid)]
        for p in witnesses:
            p.hold_filter = lambda method, body: method == "spend"
        with self.assertRaises(SealFailed):
            run._transact(alice, refs, outputs, bob)
        for p in witnesses:
            p.hold_filter = None
        t1 = next(iter(alice.pending))
        time.sleep(run.cfg.pledge_ttl + run.cfg.max_skew + 1.5)
        alice.release_expired_pledges()
        self.assertTrue(any(r[:3] == (sigil, 0, t1) for r in run.released), "rule 3 released the pledge")
        self.assertEqual(run.op_succession(random.Random(3)), "ok")
        bound = [RemoteWitness(u).status(sigil)["tid"] for u in run.directory[cid]]
        self.assertNotIn(t1, bound, "the successor's members are bound to the released transition")

    @unittest.expectedFailure
    def test_released_pledge_completed_by_replay_after_succession(self):
        """FINDING (same root cause as ``test_released_pledge_resurrected_by_succession``):
        the network adversary that held alice's lost T1 requests replays them after the
        succession. The new committee re-acknowledges the binding it inherited and the new
        members vote the binding they hold (no expiry check applies to an existing binding),
        so T1 is sealed -- a payment alice released under rule 3 -- while alice's wallet still
        counts the coin as hers (S4: a holding consumed by a complete transition). With
        alice's later payments of that coin refused forever, the coin is in effect paid to bob
        behind its owner's back. Same suggested fix."""
        import json as _json
        from sigil.wallet import mirror_acks
        run = self.scenario(kinds="mixed", committee=True, dead_man=3)
        alice, bob = run.wallets["alice"], run.wallets["bob"]
        cid = run.cids[0]
        asset = next(a for a in run.assets if alice.balance(a) > 0)
        refs, outputs = alice.payment_outputs(asset, 5, bob.address())
        old = [run.c.proxies[i] for i in run.c.indices(cid)]
        for p in old:
            p.hold_filter = lambda method, body: method == "spend"
        with self.assertRaises(SealFailed):
            run._transact(alice, refs, outputs, bob)
        for p in old:
            p.hold_filter = None
        held = [_json.loads(h[3])["request"] for p in old for h in p.held if h[4]]
        for p in old:
            p.drop_held()
        time.sleep(run.cfg.pledge_ttl + run.cfg.max_skew + 1.5)
        alice.release_expired_pledges()
        self.assertEqual(run.op_succession(random.Random(3)), "ok")
        req = {k: v for k, v in held[0].items() if k != "mirror"}
        acks = mirror_acks(run.mallory.network, req)            # any client can ask the new committee
        if acks:
            req["mirror"] = acks
        for u in run.directory[cid]:
            try:
                RemoteWitness(u).spend(req)
            except Rejected:
                pass
        found = kinds_of(self.check(run))
        self.assertNotIn("S4-holding-already-consumed", found)
    @unittest.expectedFailure
    def test_swap_interrupted_after_kill_switches_never_settles(self):
        """FINDING (Medium-High, liveness: honest funds locked for good by a transient fault;
        found by the long run, e.g. ``--seeds 13,33,47,68,69`` with ``--ops 30``: their stuck
        pledges all belong to swaps; reproduced here deterministically).

        Scenario: alice (home X) and bob (home Y) run ``sigil.swap.atomic_swap``'s steps. The
        main inputs are sealed; both release their kill switches (``authorise(...,
        release_kill=True)``, which pledges them); while the kill switches are being sealed
        every SPEND *reply* is lost (the witnesses bind and vote, the client sees a dead
        connection). The swap raises ``SealFailed``. The network heals; both wallets call
        ``release_expired_pledges`` repeatedly.

        What happens: every input of the swap is bound -- and at the witnesses actually
        sealed -- to the swap, so no pledge can be released (rule 3) and no death proof
        exists. ``Wallet._settle`` re-authorises with ``authorise(header, body, extra)``:
        without ``release_kill`` it withholds the kill switch's unlock, and it never has the
        counter-party's unlocks (``atomic_swap`` does not pass them as ``extra``), so every
        re-seal is refused ("lock not satisfied"); ``abort`` finds no death proof and
        ``_pull_kill_switch`` skips kill switches already pledged. Neither party ever
        finalises: the swap is complete at the witnesses (the inputs are consumed), yet both
        wallets keep the inputs pledged and never receive the outputs.

        Impact: both parties' coins (and their kill switches) are locked permanently by a
        transient network fault, with no adversary; the other party's outputs are lost to it.
        The same root cause strands the transaction ``abort`` builds to spend a kill switch
        elsewhere (``Wallet._pull_kill_switch``, ``release_kill=True``) when only some witnesses
        bound it before a fault: ``_settle`` re-authorises it without the kill switch's unlock,
        forever (long-run seeds 209 and 225).

        Suggested fix: persist the whole multi-party authorisation in each party's ``pending``
        (pass every party's unlocks as ``extra``), let ``_settle`` re-authorise a kill switch
        that is already pledged to the same tid (``release_kill=True`` for it), and when
        re-sealing fails because a binding exists, assemble the seal from the votes the
        witnesses report in STATUS (``find_votes``) instead of requiring fresh votes.
        """
        from sigil.swap import propose_swap
        run = self.scenario(kinds="mixed")
        a, b = run.wallets["alice"], run.wallets["bob"]
        x = next(z for z in run.assets if a.balance(z) > 0)
        y = next(z for z in run.assets if b.balance(z) > 0)
        header, body, _terms = propose_swap(a, x, 10, b, y, 10)
        tid = model.transition_id(header)
        sigils = {s for s, _ in header["inputs"]}
        unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
        kills = (a.kill_switches | b.kill_switches) & sigils
        a.seal(header, body, unlocks, only=sigils - kills)
        unlocks.update({**a.authorise(header, body, release_kill=True), **b.authorise(header, body, release_kill=True)})
        for p in run.c.proxies.values():
            p.faults.only, p.faults.p_lose_reply = ("spend",), 1.0
        with self.assertRaises(SealFailed):
            a.seal(header, body, unlocks, only=kills)
        for p in run.c.proxies.values():
            p.faults.clear()
        time.sleep(run.cfg.pledge_ttl + run.cfg.max_skew + 1.5)
        for _ in range(3):
            for w in (a, b):
                w.release_expired_pledges()
        self.assertEqual((run._live_pledges(a), run._live_pledges(b)), ({}, {}), "the swap's pledges never settle")
        self.assertIn(tid, a.dossier.transitions)
        self.assertIn(tid, b.dossier.transitions)

    @unittest.expectedFailure
    def test_failed_succession_attempt_halts_a_live_home(self):
        """FINDING (Medium, liveness; found by seed 39 of the long run, ``--seeds 39 --ops 30``,
        whose succession attempt failed and whose home then never voted again; reproduced
        here deterministically).

        Scenario: a home with a committee of 4 (q_k = 3). Its members are cut off from the
        committee's heartbeat probes for longer than ``dead_man``, but two standby members
        restart meanwhile (a restart starts a new observation window, SPEC §5.5), so only
        two of them consider the home dead. The operator tries ``RemoteNetwork.succeed``:
        each standby member is asked to SUCCEED on its own, the two that agree sign and
        *fence* at once, the other two refuse, and the call fails ("not enough standby members
        agree"). The partition heals; the home is alive.

        What happens: the two fenced members never acknowledge anything for the version
        again, so at most two acks can be collected and a witness needs three (mirror before
        vote): the live home can never vote again. It can only be retired by completing *that
        same* successor body (a cooperative rotation to exactly those new members, which the
        failed attempt's operator may no longer have), so the failed attempt silently decided
        the home's fate.

        Impact: one failed or premature succession attempt (a timing mistake, not an attack)
        halts every payment of a live constellation.

        Suggested fix: make succession two-phase in the client: ask every standby member
        whether it *would* sign (a read-only ``dead`` flag in ``/v0/info`` or a dry-run SUCCEED)
        and send SUCCEED only once a quorum would; and document that a successor body some
        member already signed must be completed, never abandoned (SPEC §5.5 / WIRE.md).
        """
        from sigil.server import RemoteNetwork
        from .cluster import TOKEN
        run = self.scenario(kinds="mixed", committee=True, dead_man=3)
        c, cid = run.c, run.cids[0]
        home = c.indices(cid)
        for i in home:
            c.probes[i].faults.partition = "refuse"
        time.sleep(run.cfg.dead_man + 1.5)
        ks = c.indices(cid, role="standby")
        for i in ks[:2]:          # these two start a new observation window
            c.kill(i)
            self.assertTrue(c.restart(i))
        new_urls = run._start_new(c.add_members(cid, ["rust", "python", "rust", "python"]))
        net = RemoteNetwork({cid: list(run.directory[cid])}, committees={cid: list(run.committees[cid])},
                            timeout=5)
        with self.assertRaises(RuntimeError):
            net.succeed(cid, new_urls, TOKEN)
        for i in home:
            c.probes[i].faults.partition = None
        self.assertEqual(sum(RemoteStandby(u).info()["fenced"] for u in run.committees[cid]), 2)
        time.sleep(1.5)
        try:
            with run._locked("alice", "bob"):
                self.pay(run, "alice", "bob", 1)     # the home is alive: this should seal
        except SealFailed as e:
            self.fail(f"the live home no longer seals after the failed succession attempt: {e}")


if __name__ == "__main__":
    unittest.main()
