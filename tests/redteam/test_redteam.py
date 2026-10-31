"""unittest entry for the red-team harness.

The default run is fast (< ~20 s): a small schedule-explorer sweep, a short
conservation fuzz, resource sanity, and mutation checks that prove the harness
catches seeded bugs. Longer runs are driven by ``python -m tests.redteam.runner``
with the env knobs documented there.

Three currently-failing findings are recorded as ``expectedFailure`` tests, each
with a precise docstring (scenario / impact / suggested fix). They do not weaken
any existing test; ``unittest discover`` stays green because an expected failure
counts as a pass.
"""

import os
import unittest
from unittest import mock

from sigil import Network, Wallet, KeyPair, locks, model
from sigil.validate import InvalidDossier
from sigil.witness import Rejected, Witness

from tests.redteam import conserve, model as rt, resources

FAST_SEEDS = int(os.environ.get("SIGIL_REDTEAM_SEEDS", "12"))
FAST_STEPS = int(os.environ.get("SIGIL_REDTEAM_STEPS", "120"))


class ScheduleExplorer(unittest.TestCase):
    """S1 (no double consumption) and S2 (honest never equivocates) within the
    fault bound, against the real witness code."""

    def test_within_fault_bound_holds(self):
        for n in (4, 7):
            viol, stats = rt.explore(FAST_SEEDS, FAST_STEPS, n=n)
            self.assertIsNone(viol, f"n={n}: {viol}")
            self.assertGreater(stats["steps"], 0)

    def test_crash_restart_holds(self):
        viol, _ = rt.explore(max(4, FAST_SEEDS // 2), FAST_STEPS, use_store=True)
        self.assertIsNone(viol, str(viol))

    def test_beyond_fault_bound_breaks_safety(self):
        """Sanity that the math, not luck, is what protects: with b = f+1 the
        quorum-intersection guarantee is gone and the explorer finds a double
        spend. (Confirms S1 has teeth.)"""
        viol, _ = rt.explore(60, 150, n=4, byz=2, allow_rotation=False)
        self.assertIsNotNone(viol)
        self.assertEqual(viol["invariant"], "S1")


class ConservationFuzz(unittest.TestCase):
    def test_honest_economy_conserves(self):
        viol, stats = conserve.run(6, 40)
        self.assertIsNone(viol, str(viol))
        self.assertGreater(stats["payments"], 0)


class MutationChecks(unittest.TestCase):
    """Seed a bug into the real witness and confirm the harness catches it."""

    def test_catches_accept_any_death_proof(self):
        with mock.patch("sigil.witness.proves_dead", lambda *a, **k: True):
            viol, _ = rt.explore(60, 150, allow_rotation=False)
        self.assertIsNotNone(viol, "mutant not caught")
        self.assertEqual(viol["invariant"], "S1")

    def test_catches_amnesiac_generation(self):
        orig = Witness.spend

        def amnesiac(self, req):
            for r in self.records.values():
                r.gen = 0
            return orig(self, req)

        with mock.patch.object(Witness, "spend", amnesiac):
            viol, _ = rt.explore(40, 150, allow_rotation=False)
        self.assertIsNotNone(viol, "mutant not caught")
        self.assertEqual(viol["invariant"], "S2")


class Resources(unittest.TestCase):
    def test_spend_cpu_amplification_measured(self):
        rows = resources.spend_cpu_amplification()
        worst = max(r["verifies"] for r in rows)
        # One sub-MiB request forces thousands of signature checks (loose bound
        # so timing jitter never fails the build).
        self.assertGreaterEqual(worst, 1000)

    def test_storage_amplification_measured(self):
        r = resources.storage_per_spend()
        self.assertGreaterEqual(r["stored_bytes"], 500_000)


# ---------------------------------------------------------------- findings
# Real defects the harness surfaced. Per the task: DO NOT FIX in sigil/; record
# each as an expectedFailure asserting the property that *should* hold.


class Finding1Conservation(unittest.TestCase):
    @unittest.expectedFailure
    def test_warm_recipient_cannot_be_inflated(self):
        """BUG-1 (CRITICAL -- conservation / counterfeit).

        Scenario: ``sigil.validate.Verifier`` memoises verified transition ids
        in ``self._ok``. On a cache hit (``_verify``: ``if cur in self._ok``) it
        pops the id and reuses ``dossier.output()`` / the body supplied in the
        *current* dossier WITHOUT re-checking ``transition_id(header) == tid``,
        ``body_hash(body) == header.body`` or the genesis supply rule. A
        transition id is just a string key; the dossier entry under it is not
        bound to the body that was originally verified.

        A malicious payer therefore supplies, under a tid the victim has already
        verified (e.g. the asset genesis, whose id is public), a *different* body
        with an extra output minted from thin air, references it, and pays
        normally. The warm recipient skips re-validation and credits the forged
        amount. Here a 1000-supply asset inflates a recipient's balance to ~1e9.
        A cold recipient (empty cache) correctly rejects ("transition does not
        match its id"), which is why the full suite otherwise passes.

        Impact: breaks conservation (SPEC Section 6.5) and the whitepaper's
        "holders check conservation" defence; counterfeits value / inflates any
        recipient that has seen the ancestor before. No witness or key is needed.

        Suggested fix: make the hash-identity and genesis checks independent of
        the cache -- e.g. in ``Verifier._verify``, before the ``self._ok``
        short-circuit, verify ``model.transition_id(tx["header"]) == cur`` and
        ``model.body_hash(tx["body"]) == tx["header"]["body"]`` for the dossier
        entry actually presented; or cache the verified (header, body) and
        compare identity on a hit. Alternatively reject any dossier containing a
        transition whose stored body does not hash to its key, up front.
        """
        issued, credited = conserve.cache_attack()
        self.assertLessEqual(credited, issued)


class Finding2InducedEquivocation(unittest.TestCase):
    @unittest.expectedFailure
    def test_lying_status_cannot_strand_an_honest_holder(self):
        """BUG-2 (MEDIUM -- liveness / griefing; third-party harm).

        Scenario: a Byzantine witness within the fault bound (f=1 of n=4) binds a
        sigil like an honest witness but always answers STATUS "unbound". During a
        partition (the honest majority briefly unreachable), an honest owner's
        first payment reaches only this liar, which binds+votes tid1 at gen 0.
        After expiry the owner runs the SPEC Section 4 rule-3 pledge release:
        every member answers STATUS and none *reports* a binding/vote, so the
        owner drops the pledge -- but the liar is hiding tid1. The owner re-pays
        the same coin as tid2, which the honest quorum seals, and an innocent
        third party (bob) receives a fully valid, quorum-sealed payment.

        On the next charter rotation, ADOPT sees two bound siblings at gen 0
        (tid1 from the liar, tid2 from the honest quorum), neither proven dead, so
        the record becomes CONTESTED. Every honest *current* witness now reports
        the ancestry input as CONTESTED, so deep confirmation (SPEC Section 9) --
        which assumes at most f faulty *current* members -- fails on an honestly
        sealed input, and a deep-confirming recipient rejects bob's valid money.

        Safety (no double spend) is preserved: tid1 can never seal. The harm is
        that the whitepaper's "only the equivocator loses" is violated -- the
        owner was *induced* to equivocate by a lying witness, and the loss lands
        on bob. Root cause: pledge release (rule 3) and deep confirmation trust
        STATUS answers, a stronger assumption than the safety theorem needs; a
        reachable Byzantine member can lie on STATUS.

        Suggested fix: do not treat a witness's STATUS word as authoritative for
        liveness decisions. For rule 3, require the owner to keep the pledge
        unless it holds a death proof (signed evidence) OR to re-use the same tid;
        and have ADOPT/deep-confirmation treat a sibling that is only ever
        attested by <= f members (never a quorum, never a seal) as a non-binding
        attempt rather than a live candidate, so a single lying witness cannot
        contaminate an honestly sealed binding. At minimum, document that rule 3
        assumes honest STATUS from reachable members.
        """
        net = Network()
        c = net.create_constellation("c", 4, byzantine={3: _LyingWitness})
        alice, bob = Wallet("a", net, c), Wallet("b", net, c, deep_threshold=1)
        usd = alice.issue("USD", 100)
        honest = net.all_witnesses(c)[:3]

        net.down = {w.pk for w in honest}          # partition: only the liar is reachable
        with self.assertRaises(Exception):
            alice.pay(bob, usd, 100)
        net.down = set()
        net.clock.advance(alice.pledge_ttl + alice.max_skew + 1)
        alice.release_expired_pledges()            # liar lies -> pledge dropped
        tid = alice.pay(bob, usd, 100)             # honest quorum seals tid2
        self.assertEqual(bob.balance(usd), 100)

        net.rotate(c, [KeyPair.generate() for _ in range(4)])
        carol = Wallet("c", net, c, deep_threshold=1)
        bob.pay(carol, usd, 100)                   # raises InvalidDossier today


class Finding3MalformedLeak(unittest.TestCase):
    @unittest.expectedFailure
    def test_spend_only_rejects_on_malformed_unlock(self):
        """BUG-3 (LOW -- robustness / contract).

        Scenario: ``sigil.witness.authorises`` catches only
        ``(KeyError, TypeError, ValueError)``. A malformed request whose
        ``unlock`` is a non-dict (e.g. a list or ``None``) reaches
        ``auth["unlock"].get("expires")``, which raises ``AttributeError`` --
        not caught -- so an in-process ``Witness.spend`` propagates
        ``AttributeError`` instead of ``Rejected``.

        Impact: low. Over HTTP the server's broad ``except`` masks it as a 400,
        and no state is mutated (it raises during authorisation parsing). But it
        breaks the documented contract (``authorises`` "return the (gen, tid) it
        binds, or None"; conformance claims malformed requests never "leak
        exceptions") and would surprise any in-process caller.

        Suggested fix: add ``AttributeError`` to the ``except`` in
        ``authorises``, or guard ``isinstance(auth.get("unlock"), dict)`` before
        ``.get``.
        """
        net = Network()
        c = net.create_constellation("c", 4)
        w = net.witnesses(c)[0]
        owner = KeyPair.generate()
        p = model.parcel(c, "x", 1, locks.sig(owner.pk), "00" * 16)
        s = model.sigil_of(p)
        hd = {"inputs": [[s, 0]], "body": "11" * 32}
        req = {"sigil": s, "header": hd, "home": c, "lock": p["lock"],
               "salt": "00" * 16, "unlock": []}   # non-dict unlock
        with self.assertRaises(Rejected):
            w.spend(req)


class _LyingWitness(Witness):
    """Byzantine within f: binds like an honest witness, but STATUS always
    reports the sigil unbound (used only by Finding 2)."""

    def status(self, sigil):
        return {"gen": 0, "tid": None, "votes": []}


if __name__ == "__main__":
    unittest.main()
