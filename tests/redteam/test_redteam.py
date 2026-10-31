"""unittest entry for the red-team harness.

The default run is fast (< ~20 s): a small schedule-explorer sweep, a short
conservation fuzz, resource sanity, and mutation checks that prove the harness
catches seeded bugs. Longer runs are driven by ``python -m tests.redteam.runner``
with the env knobs documented there.

Five currently-failing findings (BUG-1, 3, 4, 5, 6) are recorded as
``expectedFailure`` tests, each with a precise docstring (scenario / impact /
suggested fix); BUG-2 was fixed upstream and is a plain regression test. They do
not weaken any existing test; ``unittest discover`` stays green because an
expected failure counts as a pass. When a fix lands, the test reports an
"unexpected success": remove its marker so it becomes a regression test.
"""

import os
import unittest
from unittest import mock

from sigil import Network, Wallet, KeyPair, locks, model
from sigil.swap import propose_swap
from sigil.wallet import SealFailed
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
    def test_lying_status_cannot_strand_an_honest_holder(self):
        """BUG-2 (MEDIUM, liveness / third-party griefing). FIXED UPSTREAM in
        91269ff / eca6edd ("contested-record settlement by seal"); now a
        regression test. Found independently by this review.

        Scenario: a Byzantine witness within the fault bound (f=1 of n=4) binds a
        sigil like an honest witness but always answers STATUS "unbound". During a
        partition only this liar is reachable, so an honest owner's first payment
        binds tid1 at the liar alone. After expiry the owner runs the SPEC
        Section 4 rule-3 pledge release: every member answers and none *reports*
        a binding, so the pledge is dropped, but the liar is hiding tid1. The
        owner re-pays the coin as tid2, which the honest quorum seals, and an
        innocent third party (bob) receives a valid payment.

        On rotation, ADOPT sees two bound siblings at gen 0 and makes the record
        CONTESTED. Before the fix every honest current witness reported the
        ancestry input as CONTESTED, so deep confirmation failed on honestly
        sealed history and a deep-confirming recipient rejected bob's money: the
        loss landed on a third party, not the (induced) equivocator.

        The fix lets ``deep_confirm`` present the seal it holds, and the witness
        settles a CONTESTED record onto the sealed candidate (SPEC Section 8
        Lemma 1). Residual (documented, not a test): rule 3 still trusts STATUS,
        so a liar can still induce a second owner signature at one generation;
        it just no longer strands anyone.
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
        s = bob.dossier.transitions[tid]["header"]["inputs"][0][0]

        net.rotate(c, [KeyPair.generate() for _ in range(4)])
        # The induced second binding still makes the record contested ...
        self.assertEqual(net.witnesses(c)[0].status(s)["tid"], "!contested")
        # ... but a deep-confirming recipient settles it with the seal and accepts.
        carol = Wallet("c", net, c, deep_threshold=1)
        bob.pay(carol, usd, 100)
        self.assertEqual(carol.balance(usd), 100)


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


class Finding4DeepConfirmSplit(unittest.TestCase):
    @unittest.expectedFailure
    def test_deep_threshold_applies_to_the_whole_payment(self):
        """BUG-4 (MEDIUM, policy evasion of the long-range-forgery defence).

        Scenario: ``Wallet.receive`` decides per *parcel* whether to run deep
        confirmation: ``p["amount"] >= self.deep_threshold``. A payer who wants to
        avoid deep confirmation (for example to pass a long-range forgery built
        from retired witness keys, SPEC Section 9) simply splits one large payment
        into many parcels each just below the threshold. Here a wallet with
        ``deep_threshold=1000`` accepts 9 990 units as 10 parcels of 999 and runs
        deep confirmation zero times.

        Impact: the SPEC Section 9 defence the holder configured for "large
        receipts" is bypassed at no cost; it is exactly the kind of parameter an
        automated adversary probes first.

        Suggested fix: apply the threshold to the total value received in one
        ``receive`` call (and, ideally, per counter-party per time window), and
        deep-confirm every parcel of a payment whose total crosses it.
        """
        net = Network()
        c = net.create_constellation("c", 4)
        m, b = Wallet("m", net, c), Wallet("b", net, c, deep_threshold=1000)
        u = m.issue("USD", 10_000)
        addrs = [b.address() for _ in range(10)]
        refs, total = m.select(u, 9990)
        outs = [model.parcel(c, u, 999, a["lock"], a["salt"]) for a in addrs]
        ch = m.address()
        outs.append(model.parcel(c, u, total - 9990, ch["lock"], ch["salt"]))
        tid = m.transact(refs, outs)
        with mock.patch.object(Wallet, "deep_confirm") as dc:
            b.receive(m.dossier.ancestry([tid]), [model.ref(tid, i) for i in range(10)])
        self.assertEqual(b.balance(u), 9990)
        self.assertGreater(dc.call_count, 0)


class Finding5SwapHostage(unittest.TestCase):
    @unittest.expectedFailure
    def test_honest_party_recovers_after_counterparty_vanishes(self):
        """BUG-5 (MEDIUM-HIGH, protocol: recovery / atomicity; hostage).

        Scenario: in a two-party swap the parties exchange unlocks. A malicious
        counter-party that receives the honest party's unlock submits *only the
        honest input* to its home's witnesses (binding it to the swap's tid) and
        then never signs or submits its own input, and never spends it elsewhere.
        The swap can never complete, but no death proof exists either: a death
        proof needs another input of the swap sealed to a different transition at
        its generation, or a quorum of votes for one (SPEC Section 3.9), and only
        the counter-party can create that. Expiry does not help: it only stops a
        witness from *newly* binding (SPEC Section 5.1); the honest input is
        already bound and stays bound. ``Wallet.abort`` raises "no proof that the
        transition is dead", and the honest coin is locked for as long as the
        counter-party likes (a free option or ransom). No equivocation, no
        Byzantine witness and no network fault are needed.

        This contradicts the whitepaper Section 7 table ("A dishonest owner ...
        cannot hurt anyone else; honest co-signers recover through release") and
        is distinct from the Section 10.7 "pathological split", which needs
        equivocation plus unreachable witnesses.

        Suggested fix (protocol): each party adds a small *kill-switch* input it
        controls to the swap and withholds that input's unlock until it sees the
        other side's inputs bound; if the counter-party stalls, it spends the
        kill switch elsewhere at the swap's generation, which yields the death
        proof. Wallets should build swaps this way by default (``sigil/swap.py``
        currently signs both sides in one process, which hides the issue).
        Alternatively, never hand over an unlock before holding the other side's.
        """
        net = Network()
        c = net.create_constellation("c", 4)
        alice, mallory = Wallet("a", net, c), Wallet("m", net, c)
        ua = alice.issue("A", 100)
        um = mallory.issue("M", 100)
        header, body, _terms = propose_swap(alice, ua, 100, mallory, um, 100)
        unlocks = alice.authorise(header, body)      # alice hands her unlock over
        r0 = body["inputs"][0]
        p0 = alice.dossier.output(r0)
        s0 = model.sigil_of(p0)
        req = {"sigil": s0, "header": header, "home": c, "lock": p0["lock"],
               "salt": p0["salt"], "unlock": unlocks[s0]}
        for w in net.witnesses(c):                   # mallory binds only alice's input
            w.spend(req)
        net.clock.advance(10_000)                    # long past every expiry
        released = alice.abort(header)               # raises today: no death proof
        self.assertIn(s0, released)


class Finding6BondSelfClaim(unittest.TestCase):
    @unittest.expectedFailure
    def test_equivocator_cannot_recover_its_own_bond(self):
        """BUG-6 (HIGH, economics: slashing is void against the cheater).

        Scenario: a witness bond is a parcel locked
        ``any(all(sig(operator), after(unbond)), equivocation(witness))``
        (whitepaper Section 7, SPEC Section 9 "Bond homes"): whoever holds an
        equivocation proof claims it. The party that holds that proof *first* is
        the equivocator itself; it signed both votes. So the operator equivocates
        and, in the same breath, spends its own bond to an address it controls
        through the equivocation branch. The witnesses of the bond's home vote
        for the first valid request they see; honest behaviour gives the
        cheater the bond back. Here the claim is sealed by the bond home's
        honest quorum.

        A related issue: the equivocation branch is not bound to the claimant
        (only ``sig``/``multi`` leaves sign the tid), so any party who sees a
        bounty claim in flight, including the bond home's witnesses, who see
        lock, salt and unlock in the SPEND request, can race it with its own
        transition. This contradicts the whitepaper's "witnesses can't front-run
        what they can't read": for non-signature branches they can read it.

        Impact: the only economic penalty in the protocol does not penalise; an
        operator coordinating a double spend at or above f can recover its
        bonds. The lock language cannot constrain outputs (no covenants), so the
        claimant always chooses where the bond goes.

        Suggested fix: never let the slashing branch be satisfied by the proof
        alone. Require a co-signature from parties independent of the operator,
        e.g. ``all(equivocation(w), multi(k, auditors))`` or a victims' / burn
        committee key, and give the operator branch a delay longer than the time
        to publish a proof. Longer term, a holder-checked covenant on the
        slashing branch (outputs must burn or pay a fixed pool).
        """
        net = Network()
        c = net.create_constellation("c", 4)
        bonds = net.create_constellation("bonds", 4)
        operator = Wallet("op", net, bonds)
        usd = operator.issue("USD", 1000)
        witness = net.witnesses(c)[0]                # run by the same operator
        okey = operator.fresh_key()
        bond_lock = locks.any_of(
            locks.all_of(locks.sig(okey.pk), locks.after(int(net.clock()) + 10 ** 8)),
            locks.equivocation(witness.pk))
        refs, outs = operator.payment_outputs(usd, 500, {"home": bonds, "lock": bond_lock,
                                                         "salt": "ab" * 16})
        btid = operator.transact(refs, outs)
        # The operator's witness equivocates, so the operator holds the proof first.
        proof = {"a": witness._vote("ff" * 32, 0, "aa" * 32),
                 "b": witness._vote("ff" * 32, 0, "bb" * 32)}
        r = model.ref(btid, 0)
        p = operator.dossier.output(r)
        s = model.sigil_of(p)
        dest = operator.address()
        header, body, _ = operator.prepare(
            [r], [model.parcel(bonds, usd, 500, dest["lock"], dest["salt"])], gens={s: 0})
        unlock = locks.empty_unlock(int(net.clock()) + 600)
        unlock["equivocations"] = [proof]
        with self.assertRaises(SealFailed):          # today: sealed, cheater keeps its bond
            operator.seal(header, body, {s: unlock})


class _LyingWitness(Witness):
    """Byzantine within f: binds like an honest witness, but STATUS always
    reports the sigil unbound (used only by Finding 2)."""

    def status(self, sigil):
        return {"gen": 0, "tid": None, "votes": []}


if __name__ == "__main__":
    unittest.main()
