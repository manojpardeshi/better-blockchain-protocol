"""Wallet bugs found by verifying the wallet (docs/VERIFICATION.md, "Wallet").

Every test here is a precise, deterministic reproduction against the REAL
code (sigil/wallet.py, sigil/wallet_store.py, sigil/swap.py) and is marked
``unittest.expectedFailure``: it asserts the CORRECT behaviour, so it fails
today and starts passing (an "unexpected success") once the bug is fixed --
at which point the marker must be removed. Each docstring gives the
scenario, the impact and a suggested fix. Severity is in the first line.

Several of them were found first by the TLA+ model of the wallet
(formal/SigilWallet.tla, the ``MC_wallet_*_mutant`` configs reproduce them at
the model level) or by the randomised conformance run of the real wallet
(tests/test_wallet_conformance.py).
"""

import copy
import os
import tempfile
import unittest
from unittest import mock

from sigil import InvalidDossier, KeyPair, Network, SealFailed, Wallet
from sigil import locks, model, wallet_store
from sigil.swap import _pays, propose_swap
from sigil.validate import Dossier
from sigil.wallet import request_seal
from sigil.witness import CONTESTED, Witness
from tests.adversary import Equivocator, Silent
from tests.test_security import manual_spend


class Crash(Exception):
    """Stands in for the wallet process dying."""


def tmpdir(case: unittest.TestCase) -> str:
    d = tempfile.TemporaryDirectory()
    case.addCleanup(d.cleanup)
    return os.path.join(d.name, "wallet")


def owner_binds(net: Network, cid: str, sigil: str) -> dict:
    """gen -> set of tids that honest-code witnesses bound on the owner's authorisation."""
    out: dict[int, set] = {}
    for w in net.all_witnesses(cid):
        rec = w.records.get(sigil)
        for e in (rec.log if rec else []):
            if e.get("kind") == "bind":
                out.setdefault(e["gen"], set()).add(model.transition_id(e["auth"]["header"]))
    return out


def rogue_counterfeit(net: Network, X: str, victims: list) -> list:
    """Mallory turns 10 real USD into a parcel homed at her own one-witness
    constellation R, then 'spends' that parcel once per victim: R's only
    witness signs anything, so every spend is sealed. Returns
    ``[(victim, dossier, ref, asset)]``; together they carry 10 USD per victim."""
    mallory = Wallet("mallory", net, X)
    usd = mallory.issue("USD", 10)
    R = net.create_constellation("rogue", 1, witness_cls=Equivocator)
    a = mallory.address(R)
    refs, _ = mallory.select(usd, 10)
    mallory.transact(refs, [model.parcel(R, usd, 10, a["lock"], a["salt"])])
    held = next(iter(mallory.holdings.values()))
    out = []
    for v in victims:
        addr = v.address(X)
        h, b, u, reqs = manual_spend(mallory, [held["ref"]],
                                     [model.parcel(X, usd, 10, addr["lock"], addr["salt"])], memo=v.name)
        mallory.dossier.add_seal(request_seal(net, reqs[0]))
        tid = mallory.dossier.add_transition(h, b, u)
        mallory.dossier.add_charters(net.registry, [R, X])
        d = Dossier.from_json(mallory.dossier.ancestry([tid]).to_json())
        out.append((v, d, model.ref(tid, 0), usd))
    return out


# ---------------------------------------------------------------------------
# (c) holdings / balance only reflect parcels a holder-side validator accepts
# ---------------------------------------------------------------------------

class TrustPolicyTests(unittest.TestCase):
    @unittest.expectedFailure
    def test_restarted_wallet_keeps_its_trust_policy(self):
        """CRITICAL. wallet_store.load drops the wallet's trust policy.

        Scenario: Alice's wallet trusts only her home X (``trusted={X}``) and is
        saved and reloaded (as every CLI command does). ``wallet_store.load``
        builds ``Wallet(name, network, home, deep_threshold=...)`` without
        ``trusted``, i.e. ``trusted=None`` = "trust any charter in the
        registry" -- and ``Verifier.verify_parcel`` adds every charter chain a
        received dossier carries to that registry (version 0 needs no
        signatures). Mallory makes a one-witness constellation R, moves 10
        real USD into an R-homed parcel and 'spends' it once per victim; R's
        witness seals all of them.

        Impact: the reloaded wallet accepts counterfeit money (unbounded
        double spends of one parcel), violating SPEC Section 6 ("the holder
        MUST also trust its home"). Before the reload the same payment is
        rejected.

        Fix: persist the trust policy (``trusted`` and convicted witnesses)
        in state.json and restore it in ``load``; refuse to load a wallet
        with no explicit policy.
        """
        net = Network()
        X = net.create_constellation("orion")
        alice = Wallet("alice", net, X, trusted={X})
        path = tmpdir(self)
        wallet_store.save(alice, path)
        alice = wallet_store.load(path, net)
        (_, d, ref, usd), = rogue_counterfeit(net, X, [alice])
        with self.assertRaises(InvalidDossier):
            alice.receive(d, [ref])

    @unittest.expectedFailure
    def test_cli_wallet_does_not_trust_constellations_named_by_a_payer(self):
        """CRITICAL. A CLI wallet trusts every constellation a payer names.

        Scenario: ``sigil.cli cmd_init`` creates ``Wallet(name, net, home)``
        with no trust policy (there is no option for one), so every CLI
        wallet has ``trusted=None``. Two such wallets each receive a 10 USD
        payment made by double-spending ONE 10 USD parcel that Mallory moved
        to her own constellation R (see ``rogue_counterfeit``); the dossier
        itself introduces R's charter.

        Impact: both payments are accepted, so 10 real USD became 20 --
        counterfeiting, repeatable without limit. (In the in-process Network
        the registry is shared; over HTTP the dossier carries R's chain into
        ``RemoteNetwork.registry`` via ``verify_parcel``.)

        Fix: a wallet must trust only constellations its owner chose: default
        ``trusted`` to ``{home}`` (plus an explicit ``--trust CID`` list in
        the CLI), and never extend trust from charters found in a dossier.
        """
        net = Network()
        X = net.create_constellation("orion")
        bob = Wallet("bob", net, X)    # exactly what cmd_init builds
        carol = Wallet("carol", net, X)
        accepted = 0
        for victim, d, ref, usd in rogue_counterfeit(net, X, [bob, carol]):
            try:
                victim.receive(d, [ref])
                accepted += 1
            except InvalidDossier:
                pass
        self.assertEqual(accepted, 0, "a double-spent rogue-homed parcel was accepted")


class DossierIntegrityTests(unittest.TestCase):
    @unittest.expectedFailure
    def test_received_dossier_cannot_overwrite_our_own_history(self):
        """HIGH. Any payer can corrupt the wallet's own dossier (loss of funds).

        Scenario: Alice pays Mallory 10 USD (T1); Alice's 90 USD change lives
        in T1, which Mallory now knows. Mallory then pays Alice 1 GOLD and
        adds to that payment's dossier a copy of T1 with its owner unlocks
        removed. ``Wallet.receive`` verifies only the ancestry of the received
        ref, then ``Dossier.merge`` copies EVERY transition and seal of the
        received dossier over Alice's own entries (``dict.update``),
        unverified.

        Impact: Alice's balance still shows 90 USD, but every payment she
        makes from it carries the corrupted T1, so no recipient accepts it --
        and the payment's input is already consumed at the witnesses. The
        good copy of T1 is gone. Same for seals (``seals.update``).

        Fix: merge only the verified ancestry of the accepted refs, and never
        replace an entry the wallet already holds (keep the first verified
        copy; a second copy of a tid must be byte-identical or ignored).
        """
        net = Network()
        X = net.create_constellation("orion")
        alice, mallory, carol = (Wallet(n, net, X) for n in ("alice", "mallory", "carol"))
        usd, gold = alice.issue("USD", 100), mallory.issue("GOLD", 5)
        t1 = alice.pay(mallory, usd, 10)
        good = copy.deepcopy(alice.dossier.transitions[t1])
        refs, outs = mallory.payment_outputs(gold, 1, alice.address())
        tg = mallory.transact(refs, outs)
        d = Dossier.from_json(mallory.dossier.ancestry([tg]).to_json())
        d.transitions[t1] = dict(copy.deepcopy(good), unlocks={})  # not in tg's ancestry
        alice.receive(d, [model.ref(tg, 0)])
        self.assertEqual(alice.dossier.transitions[t1], good, "a payer overwrote our own transition")
        alice.pay(carol, usd, 50)
        self.assertEqual(carol.balance(usd), 50)


class ReceiveLockTests(unittest.TestCase):
    @unittest.expectedFailure
    def test_receive_rejects_a_parcel_the_payer_can_still_spend(self):
        """HIGH. A payment the payer can claw back is credited as received.

        Scenario: a merchant hands out ``address() = {home, lock: sig(m),
        salt}``. Mallory pays 100 USD to ``{home, lock: any(sig(m),
        sig(mallory)), salt}``. ``Wallet.receive`` only checks that SOME key
        of the lock is ours (``keys_in(lock) & self.keys``), so it accepts the
        parcel and ``balance`` reports 100. Mallory then spends it back with
        her own key. (Variants: ``all(sig(m), sig(mallory))`` -- unspendable
        without Mallory, a hostage; ``all(sig(m), before(t))`` -- burns at t.)

        Impact: a merchant ships goods for a payment that is not final;
        ``balance`` counts value it cannot spend (``select`` skips non-``sig``
        locks), and the payer takes it back at will.

        Fix: record every address the wallet issues and accept a received
        parcel only if its exact ``(home, lock, salt)`` is one of them (or
        only locks made solely of our own keys); use ``watch`` for anything
        else, and keep watched parcels out of ``balance``.
        """
        net = Network()
        X = net.create_constellation("orion")
        merchant, mallory = Wallet("merchant", net, X), Wallet("mallory", net, X)
        usd = mallory.issue("USD", 100)
        addr = merchant.address()
        mk = mallory.fresh_key()
        evil = dict(addr, lock=locks.any_of(addr["lock"], locks.sig(mk.pk)))
        refs, outs = mallory.payment_outputs(usd, 100, evil)
        tid = mallory.transact(refs, outs)
        try:
            merchant.receive(mallory.dossier.ancestry([tid]), [model.ref(tid, 0)])
        except InvalidDossier:
            return  # correct: not a payment to the address we issued
        # Show the impact: Mallory takes it back, the merchant still "has" it.
        mallory.watch(mallory.dossier.ancestry([tid]), model.ref(tid, 0))
        back = mallory.address()
        mallory.transact([model.ref(tid, 0)], [model.parcel(X, usd, 100, back["lock"], back["salt"])])
        self.fail(f"merchant credited {merchant.balance(usd)} USD that the payer clawed back")

    @unittest.expectedFailure
    def test_two_parcels_on_one_sigil_are_not_both_credited(self):
        """LOW. Two payments to one address are both credited; only one is spendable.

        Scenario: a payer (e.g. re-running ``sigil.cli pay`` with the same
        address file) pays the same address twice. Both parcels have the
        same sigil (it commits to home, lock and salt only). ``receive``
        accepts the second one because the sigil is not yet bound.

        Impact: ``balance`` shows 20 while at most 10 can ever be spent: once
        either parcel's sigil is consumed the other is dead, and a payment
        using both is rejected (duplicate sigil in the header).

        Fix: in ``receive``, refuse (or merge-track) a parcel whose sigil the
        wallet already holds; in ``pay``, refuse to pay an address twice.
        """
        net = Network()
        X = net.create_constellation("orion")
        alice, payer = Wallet("alice", net, X), Wallet("payer", net, X)
        usd = payer.issue("USD", 100)
        addr = alice.address()
        for _ in range(2):
            refs, outs = payer.payment_outputs(usd, 10, addr)
            tid = payer.transact(refs, outs)
            try:
                alice.receive(payer.dossier.ancestry([tid]), [model.ref(tid, 0)])
            except InvalidDossier:
                pass
        self.assertEqual(alice.balance(usd), 10, "two parcels sharing one sigil were both credited")


# ---------------------------------------------------------------------------
# (a) no self-equivocation; (f) swaps under an adversarial counter-party
# ---------------------------------------------------------------------------

class AuthoriseTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.Y = self.net.create_constellation("lyra")
        self.alice = Wallet("alice", self.net, self.X)
        self.mallory = Wallet("mallory", self.net, self.Y)
        self.usd = self.alice.issue("USD", 100)
        self.gold = self.mallory.issue("GOLD", 10)

    def pay_header(self, memo):
        held = next(iter(self.alice.holdings.values()))
        a = Wallet("payee-" + memo, self.net, self.X).address()
        return self.alice.prepare([held["ref"]], [model.parcel(self.X, self.usd, 100, a["lock"], a["salt"])], memo)

    @unittest.expectedFailure
    def test_authorise_refuses_a_header_at_another_generation(self):
        """HIGH. A counter-party's header makes the wallet equivocate.

        Scenario (found by TLC, ``formal/MC_wallet_gen_mutant.cfg``): Alice
        authorises a payment T1 of her parcel s at generation 0; its requests
        are in flight (pledge (s, 0, T1)). Mallory proposes a swap whose
        header lists Alice's s at generation 1. ``Wallet.authorise`` never
        checks a header's generation against the holding's, and its
        equivocation guard only fires for a pledge at the SAME generation,
        so it signs and OVERWRITES the pledge with (s, 1, swap). Alice's next
        payment T3 of s at generation 0 then passes the guard too.

        Impact: Alice has signed two different transitions for (s, 0) while
        T1 can still be sealed (SPEC Section 4 rules 1 and 2). Witnesses
        split between T1 and T3 can leave s stuck with neither sealed and no
        death proof; after a rotation the sigil becomes CONTESTED (SPEC 5.4).
        The wallet's OWN stale header does the same: the conformance run
        (tests/test_wallet_conformance.py) found that re-authorising a failed
        transition after ``abort`` moved the holding to generation 1 replaces
        a live generation-1 pledge -- there, one whose transition had already
        completed -- with the dead generation-0 one.

        Fix: in ``authorise``, for every input we hold require
        ``header.inputs[k] == [h["sigil"], h["gen"]]`` (sigil of the parcel
        at ``body.inputs[k]``, our generation), and refuse while ANY live
        pledge of that sigil names a different tid, whatever its generation.
        """
        h1, b1, _ = self.pay_header("t1")
        self.alice.authorise(h1, b1)                     # T1 in flight at (s, 0)
        held = next(iter(self.alice.holdings.values()))
        s = held["sigil"]
        mref = next(iter(self.mallory.holdings.values()))
        to_a, to_m = self.alice.address(), self.mallory.address()
        body = model.body([mref["ref"], held["ref"]],
                          [model.parcel(self.X, self.gold, 10, to_a["lock"], to_a["salt"]),
                           model.parcel(self.Y, self.usd, 100, to_m["lock"], to_m["salt"])], memo="swap")
        header = model.header([[mref["sigil"], 0], [s, 1]], body)   # Alice's input at generation 1
        try:
            self.alice.authorise(header, body)
        except ValueError:
            return  # correct
        h3, b3, _ = self.pay_header("t3")
        try:
            self.alice.authorise(h3, b3)
        except ValueError:
            self.fail("authorise accepted a header naming the wrong generation")
        self.fail("alice signed T1 and T3 for (s, 0) while T1 could still be sealed")

    @unittest.expectedFailure
    def test_authorise_checks_the_header_commits_to_the_body(self):
        """HIGH. Swap: the counter-party shows one body and gets a signature for another.

        Scenario: Mallory proposes a swap (header, body) where ``body`` pays
        Bob 100 USD for his 10 GOLD, so Bob's check ``swap._pays(body, ...)``
        passes. But the header she sends commits (``header.body``) to a
        DIFFERENT body that pays both inputs to Mallory. ``Wallet.authorise``
        computes the tid from the header only and never checks
        ``header["body"] == body_hash(body)``. Witnesses only ever see the
        header, so they seal Bob's input, and Mallory finalises her body.

        Impact: Bob's GOLD is gone and he receives nothing -- paid without
        being paid (property (f)). ``swap.atomic_swap`` is in-process and
        builds both sides honestly, but ``authorise`` is the wallet's only
        signing primitive and swap.py's "each party checks it is paid before
        signing" relies on it.

        Fix: ``authorise`` must check ``header["body"] == model.body_hash(body)``,
        ``len(header.inputs) == len(body.inputs)`` and that each of our inputs
        appears at its own position with its own sigil and generation.
        A cross-party swap API should also check exactly which of our inputs
        are consumed and that our change comes back (``_pays`` does not).
        """
        a, b = self.mallory, Wallet("bob", self.net, self.Y)
        gold = b.issue("GOLD", 10)
        usd = a.issue("USD", 100)
        header, body, terms = propose_swap(a, usd, 100, b, gold, 10)
        to_b = terms["b"][0]
        self.assertTrue(_pays(body, to_b, usd, 100))
        me, me2 = a.address(), a.address()
        evil_body = model.body(body["inputs"], [model.parcel(self.Y, gold, 10, me["lock"], me["salt"]),
                                                model.parcel(self.Y, usd, 100, me2["lock"], me2["salt"])],
                               memo="evil")
        evil_header = dict(header, body=model.body_hash(evil_body))
        try:
            ub = b.authorise(evil_header, body)   # Bob checked `body`, signs `evil_header`
        except ValueError:
            return  # correct
        ua = a.authorise(evil_header, evil_body)
        a.seal(evil_header, evil_body, {**ua, **ub})
        tid = a.finalise(evil_header, evil_body, {**ua, **ub})
        a.verifier.verify_transition(a.dossier, tid)
        self.fail("Mallory sealed a swap that takes Bob's GOLD and pays him nothing")


# ---------------------------------------------------------------------------
# (b)/(d) pledges, recovery and durability
# ---------------------------------------------------------------------------

class PendingTransitionTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion")
        self.bob = Wallet("bob", self.net, self.X)
        self.carol = Wallet("carol", self.net, self.X)
        self.usd = self.bob.issue("USD", 100)
        self.ws = self.net.witnesses(self.X)

    def assert_recoverable(self, wallet, s):
        """After the outage the parcel is either gone (its transition completed
        and was finalised) or spendable again."""
        wallet.release_expired_pledges()
        if any(h["sigil"] == s for h in wallet.holdings.values()):
            try:
                wallet.select(self.usd, 100)
            except ValueError:
                self.fail("the wallet shows 100 USD it can neither spend, complete nor recover")

    @unittest.expectedFailure
    def test_failed_payment_does_not_freeze_its_input(self):
        """HIGH. A transient outage during ``pay`` freezes the input forever.

        Scenario (``formal/MC_wallet_pending_mutant.cfg``): Bob pays Carol
        while 2 of the 4 witnesses are unreachable. The 2 others bind and
        vote T1; ``request_seal`` raises SealFailed. ``Wallet.transact``
        re-raises and the header and body of T1 are dropped -- they are
        never stored, not even by ``cli cmd_pay``, which persists only
        ``(gen, tid, expires)``.

        Impact: T1 is bound at 2 witnesses, so ``unpledge_if_unbound``
        refuses forever; nothing proves T1 dead, so ``abort`` is impossible
        (and needs the header anyway); and the only way out -- re-authorising
        the SAME T1 with a fresh expiry so the others bind it -- needs the
        header. Bob's 100 USD are frozen while ``balance`` reports them.
        Likewise, if a delayed request completes T1 later, Bob never learns
        it: Carol is never handed the dossier and Bob's change is lost.

        Fix: persist every pending transition (header, body, unlocks) with
        its pledge in wallet_store, and let ``release_expired_pledges`` /
        ``select`` retry it (re-authorise the same tid -- allowed by SPEC
        Section 4 rule 1 -- re-seal, finalise) and use it for ``abort``.
        """
        self.net.down.update(w.pk for w in self.ws[2:])
        with self.assertRaises(SealFailed):
            self.bob.pay(self.carol, self.usd, 100)
        s = next(iter(self.bob.pledged))
        self.net.down.clear()
        self.net.clock.advance(10 ** 6)
        self.assert_recoverable(self.bob, s)

    @unittest.expectedFailure
    def test_cli_restart_mid_seal_can_finish_the_payment(self):
        """HIGH. A CLI wallet that crashes while sealing can never finish or recover.

        Scenario: the steps of ``sigil.cli cmd_pay``: prepare, authorise,
        ``wallet_store.save`` (the pledge is durable), then the process dies
        after 2 of 4 witnesses voted. After a restart the wallet has the
        pledge ``(0, T1, expires)`` but not T1's header or body (state.json
        and dossier.json hold neither).

        Impact: as above -- the parcel is frozen forever (or, if a delayed
        request completes T1, the payment is lost to both sides).

        Fix: as above; save the header, body and unlocks before the first
        spend request, together with the pledge.
        """
        path = tmpdir(self)
        a = self.carol.address()
        refs, outs = self.bob.payment_outputs(self.usd, 100, a)
        header, body, _ = self.bob.prepare(refs, outs)
        unlocks = self.bob.authorise(header, body)
        wallet_store.save(self.bob, path)
        s = header["inputs"][0][0]
        p = self.bob.dossier.output(refs[0])
        req = {"sigil": s, "header": header, "home": self.X, "lock": p["lock"], "salt": p["salt"],
               "unlock": unlocks[s]}
        for w in self.ws[:2]:
            w.spend(req)                   # ...and here the wallet process dies
        bob = wallet_store.load(path, self.net)
        self.net.clock.advance(10 ** 6)
        self.assert_recoverable(bob, s)

    @unittest.expectedFailure
    def test_library_pay_cannot_lose_a_pledge_in_a_crash(self):
        """MEDIUM. ``Wallet.pay`` has no point at which the pledge can be saved.

        Scenario (``formal/MC_wallet_crash_mutant.cfg``): an application uses
        the library and saves the wallet after every call, as wallet_store
        advises. ``Wallet.pay`` authorises and sends spend requests in one
        call, so the pledge is in memory only while witnesses vote. The
        process dies after one witness voted T1; the restarted wallet (last
        save: before ``pay``) has no pledge and pays Dave from the same parcel
        at the same generation.

        Impact: two owner-authorised tids bound at (s, 0): self-equivocation
        (SPEC Section 4 rule 1); s can end up stuck (neither sealed) or
        CONTESTED after a rotation.

        Fix: give ``transact``/``pay`` a persistence hook invoked after
        ``authorise`` and before ``seal`` (as cli.cmd_pay does by hand), and,
        as defence in depth, refuse to authorise a fresh spend of a sigil
        while any member reports it bound or voted at that generation for a
        tid the wallet has no pledge for (the restarted wallet's STATUS check).
        """
        path = tmpdir(self)
        dave = Wallet("dave", self.net, self.X)
        wallet_store.save(self.bob, path)
        real = Witness.spend

        def dying(w, req):
            real(w, req)
            raise Crash
        with mock.patch.object(Witness, "spend", dying), self.assertRaises(Crash):
            self.bob.pay(self.carol, self.usd, 100)
        s = next(iter(self.bob.pledged))
        bob = wallet_store.load(path, self.net)
        try:
            bob.pay(dave, self.usd, 100)
        except (ValueError, SealFailed):
            pass
        self.assertLessEqual(len(owner_binds(self.net, self.X, s).get(0, set())), 1,
                             "the restarted wallet signed a second tid at (s, 0)")


class AbortTests(unittest.TestCase):
    @unittest.expectedFailure
    def test_abort_recovers_an_input_bound_at_fewer_than_a_quorum(self):
        """MEDIUM. ``abort`` cannot recover an input that only a minority bound.

        Scenario (``formal/MC_wallet_abort_mutant.cfg``, liveness): Alice and
        Mallory swap. While Alice seals, one honest witness of X is down and
        the Byzantine one stays silent, so only 2 witnesses bind Alice's
        input. Mallory double-spends her own input, so the swap is provably
        dead. ``Wallet.abort`` finds the death proof and releases the 2
        bound witnesses, but drops the pledge only if
        ``len(released) >= quorum`` (3); witnesses that never bound Alice's
        input do not count, although they already accept a spend at
        generation 1.

        Impact: the pledge stays forever -- later aborts release nobody, and
        ``unpledge_if_unbound`` refuses because the released witnesses still
        report their (dead) votes. Alice's 100 USD are frozen by a
        counter-party's betrayal plus one crash, within the fault bound.

        Fix: with a valid death proof the pledged tid can never complete
        (SPEC Section 8 Lemma 2), so drop the pledge and move to
        ``g + 1`` once the proof verifies; release every witness still bound
        (now or later) with the same proof. If SPEC Section 4 rule 2 should
        stay, count members that are unbound at <= g as ready for g + 1.
        """
        net = Network()
        X = net.create_constellation("orion", byzantine={3: Silent})
        Y = net.create_constellation("lyra")
        alice, mal, bob = Wallet("alice", net, X), Wallet("mallory", net, Y), Wallet("bob", net, X)
        usd, gold = alice.issue("USD", 100), mal.issue("GOLD", 10)
        header, body, _ = propose_swap(alice, usd, 100, mal, gold, 10)
        unlocks = {**alice.authorise(header, body), **mal.authorise(header, body)}
        me = mal.address()
        betrayal = manual_spend(mal, [body["inputs"][1]], [model.parcel(Y, gold, 10, me["lock"], me["salt"])])
        request_seal(net, betrayal[3][0])
        net.down.add(net.witnesses(X)[2].pk)
        with self.assertRaises(SealFailed):
            alice.seal(header, body, unlocks)
        net.down.clear()
        alice.abort(header)
        net.clock.advance(10 ** 6)
        alice.release_expired_pledges()
        try:
            alice.pay(bob, usd, 100)
        except (ValueError, SealFailed) as e:
            self.fail(f"alice's input stays frozen after the swap died: {e}")
        self.assertEqual(bob.balance(usd), 100)



class StatusLiar(Witness):
    """Follows the protocol but always answers STATUS with "unbound" (within f)."""

    def status(self, sigil):
        return {"gen": 0, "tid": None, "votes": []}


class RotationFindings(unittest.TestCase):
    @unittest.expectedFailure
    def test_legitimate_repledge_stays_deep_confirmable_after_rotation(self):
        """MEDIUM (wallet x witness ADOPT). A rule-3 pledge release plus one
        Byzantine log makes the sigil CONTESTED forever after a rotation.

        Scenario: Bob pays Carol (T1) while only the Byzantine witness z is
        reachable; z binds T1 (really, before expiry) but answers STATUS with
        "unbound". After expiry Bob's wallet drops the pledge exactly as SPEC
        Section 4 rule 3 allows (all members answered, none reports T1) and
        pays Dave (T3) at the same generation; the honest witnesses seal T3.
        Then the charter rotates: z's FREEZE evidence carries its genuine bind
        of T1 with Bob's valid (expired) authorisation, so ADOPT sees two
        bindings at (s, 0) and makes s CONTESTED (SPEC 5.4). T3's seal kills
        T1, but T3 itself never dies, so the record stays CONTESTED.

        Impact: deep confirmation (SPEC Section 9) of T3 -- a legitimate,
        sealed payment -- fails forever, so every coin descending from it is
        refused by deep-confirming wallets. Had the rotation happened while
        T3 was still unsealed, s would be frozen for good (nothing proves T1
        dead). Note TLC checks SigilWallet.tla without rotation and
        SigilRot.tla without expiry-based releases; this sits between them.

        Fix (witness side): let RELEASE of a CONTESTED record also accept a
        valid SEAL for a remaining candidate once every other candidate is
        proven dead, and bind the record to it (re-voting an already sealed
        tid at its own generation creates no second seal). Wallet side, an
        alternative is to move to a fresh generation instead of re-pledging
        the same one, which needs ADOPT to treat a later binding as
        superseding an earlier unsealed one.
        """
        net = Network()
        X = net.create_constellation("orion", byzantine={3: StatusLiar})
        bob, carol, dave = (Wallet(n, net, X) for n in ("bob", "carol", "dave"))
        usd = bob.issue("USD", 100)
        ws = net.witnesses(X)
        net.down.update(w.pk for w in ws[:3])     # only the liar is reachable
        with self.assertRaises(SealFailed):
            bob.pay(carol, usd, 100)
        net.down.clear()
        net.clock.advance(bob.pledge_ttl + bob.max_skew + 1)
        self.assertEqual(len(bob.release_expired_pledges()), 1)
        tid = bob.pay(dave, usd, 100)
        Wallet("erin", net, X).deep_confirm(dave.dossier, [tid])   # fine before the rotation
        net.rotate(X, [KeyPair.generate() for _ in range(4)])
        s = dave.dossier.transitions[tid]["header"]["inputs"][0][0]
        self.assertTrue(all(w.records[s].tid == CONTESTED for w in net.witnesses(X)))
        try:
            Wallet("frank", net, X).deep_confirm(dave.dossier, [tid])
        except InvalidDossier as e:
            self.fail(f"a legitimate sealed payment no longer deep-confirms: {e}")


if __name__ == "__main__":
    unittest.main()
