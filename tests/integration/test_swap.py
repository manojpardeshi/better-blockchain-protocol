"""Scenario 2: two-party atomic swaps across two mixed constellations, with kill switches."""

from sigil import model
from sigil.swap import atomic_swap, propose_swap
from sigil.validate import Dossier, InvalidDossier, TrustPolicy, Verifier
from sigil.wallet import SealFailed, Wallet
from tests.integration.harness import MIXED, IntegrationCase


class SwapTests(IntegrationCase):
    def setUp(self):
        super().setUp()
        self.X, self.x_idx = self.c.constellation("orion", MIXED)
        self.Y, self.y_idx = self.c.constellation("lyra", ["python", "rust", "rust", "python"])

    def test_atomic_swap(self):
        net = self.net()
        alice, bob = Wallet("alice", net, self.X), Wallet("bob", net, self.Y)
        carol = Wallet("carol", net, self.X, deep_threshold=1)
        usd, gold = alice.issue("USD", 1000), bob.issue("GOLD", 10)
        tid = atomic_swap(alice, usd, 100, bob, gold, 2)
        self.assertEqual((alice.balance(usd), alice.balance(gold)), (900, 2))
        self.assertEqual((bob.balance(usd), bob.balance(gold)), (100, 8))
        # Both kill switches came back to their owners in the swap's outputs.
        for w in (alice, bob):
            kills = [h for h in w.holdings.values()
                     if (w.dossier.transitions.get(h["parcel"]["asset"], {}).get("body", {}).get("genesis") or {})
                     .get("name") == "kill-switch"]
            self.assertEqual([h["parcel"]["amount"] for h in kills], [1], w)
        # bob pays on what he got from the swap; carol deep-confirms the swap's every input.
        bob.pay(carol, usd, 40)
        self.assertEqual(carol.balance(usd), 40)
        self.assertTrue(any(t == tid for _s, _g, t in carol._confirmed))
        self.check_invariants({"alice": alice, "bob": bob, "carol": carol})

    def test_counterparty_stalls_kill_switch_frees_inputs(self):
        net = self.net()
        alice, bob = Wallet("alice", net, self.X), Wallet("bob", net, self.Y)
        carol = Wallet("carol", net, self.X, deep_threshold=1)
        usd, gold = alice.issue("USD", 100), bob.issue("GOLD", 10)
        header, body, _terms = propose_swap(alice, usd, 100, bob, gold, 2)
        tid = model.transition_id(header)
        unlocks = {**alice.authorise(header, body), **bob.authorise(header, body)}
        sigils = [s for s, _g in header["inputs"]]
        a_main, b_main, a_kill, b_kill = sigils  # propose_swap's order: a's, b's, then the kill switches
        self.assertEqual({a_kill, b_kill}, (alice.kill_switches | bob.kill_switches) & set(sigils))
        # 1. Every main input is bound and sealed to the swap; no kill switch is signed yet.
        alice.seal(header, body, unlocks, only={a_main, b_main})
        # 2. bob stalls: he never releases his kill switch. alice gives up on him: she spends
        #    her own kill switch elsewhere, a death proof that frees her input.
        released = alice.abort(header)
        self.assertEqual(released, [a_main])
        for w in net.witnesses(self.X):
            st = w.status(a_main)
            self.assertEqual((st["gen"], st["tid"]), (1, None), w)
        # 3. bob comes back and releases his kill switch: too late, the swap can never complete.
        late = bob.authorise(header, body, release_kill=True)
        alice.seal(header, body, {**unlocks, **late}, only={b_kill})   # bob's own kill switch binds
        with self.assertRaises(SealFailed):
            alice.seal(header, body, {**unlocks, **late}, only={a_kill})
        # Nobody can present the stalled swap as complete: a fresh holder rejects it.
        d = Dossier().merge(alice.dossier).merge(bob.dossier)
        for s in sigils:
            seal = alice.dossier.seals.get(model.seal_key(s, tid))
            if seal:
                d.add_seal(seal)
        d.add_transition(header, body, {**unlocks, **late})
        with self.assertRaises(InvalidDossier):
            Verifier(TrustPolicy(net.registry, {self.X, self.Y})).verify_transition(d, tid)
        # 4. alice spends her freed input at generation 1; carol deep-confirms it.
        alice.pay(carol, usd, 100)
        self.assertEqual((alice.balance(usd), carol.balance(usd)), (0, 100))
        # 5. bob recovers his main input and his kill switch with the same kind of proof.
        self.assertEqual(sorted(bob.abort(header)), sorted([b_main, b_kill]))
        bob.pay(alice, gold, 2)
        self.assertEqual((alice.balance(gold), bob.balance(gold)), (2, 8))
        self.check_invariants({"alice": alice, "bob": bob, "carol": carol}, headers=[header])
