"""Agent spending-policy locks (sigil/agent_policy.py) enforced end-to-end by
the real witnesses and holder validation."""

import unittest

from sigil import Network, Wallet, locks, model
from sigil import agent_policy as ap
from sigil.wallet import SealFailed


def _spend_parcel(owner_wallet, holding, outputs, signers):
    """Build/authorise/seal a spend of one held parcel, signing with ``signers``
    (list of (wallet, pk)). Returns True if it sealed."""
    refs = [holding["ref"]]
    header, body, tid = owner_wallet.prepare(refs, outputs)
    s = holding["sigil"]
    unlock = locks.empty_unlock(int(owner_wallet.clock()) + 600)
    for w, pk in signers:
        unlock["sigs"][pk] = locks.sign_unlock(w.keys[pk], s, tid, unlock["expires"])
    try:
        owner_wallet.seal(header, body, {s: unlock})
    except SealFailed:
        return False
    owner_wallet.finalise(header, body, {s: unlock})
    return True


def _fund(net, c, issuer, lock, amount, asset):
    """Give the issuer a parcel locked with ``lock`` and return its holding."""
    addr = {"home": c, "lock": lock, "salt": "ab" * 16}
    refs, outs = issuer.payment_outputs(asset, amount, addr)
    tid = issuer.transact(refs, outs)
    r = model.ref(tid, 0)
    p = issuer.dossier.output(r)
    h = {"ref": r, "parcel": p, "sigil": model.sigil_of(p), "gen": 0}
    issuer.holdings[model.parcel_id(r)] = h
    return h


class AgentPolicyTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.c = self.net.create_constellation("c", 4)
        self.bank = Wallet("bank", self.net, self.c)
        self.usd = self.bank.issue("USD", 1_000_000)
        self.agent = self.net  # placeholder; keys live on self.bank for simplicity
        self.agent_kp = self.bank.fresh_key()
        self.owner_kp = self.bank.fresh_key()

    def _dest(self):
        a = self.bank.address()
        return [model.parcel(self.c, self.usd, 100, a["lock"], a["salt"])]

    def test_co_signed_needs_both(self):
        lock = ap.co_signed(self.agent_kp.pk, self.owner_kp.pk)
        h = _fund(self.net, self.c, self.bank, lock, 100, self.usd)
        self.assertFalse(_spend_parcel(self.bank, h, self._dest(),
                                       [(self.bank, self.agent_kp.pk)]))
        self.assertTrue(_spend_parcel(self.bank, h, self._dest(),
                                      [(self.bank, self.agent_kp.pk), (self.bank, self.owner_kp.pk)]))

    def test_threshold_multisig(self):
        cosigners = [self.bank.fresh_key() for _ in range(3)]
        lock = ap.threshold_multisig(self.agent_kp.pk, [k.pk for k in cosigners], 2)
        h = _fund(self.net, self.c, self.bank, lock, 100, self.usd)
        # agent + 1 cosigner: not enough (needs 2 of 3)
        self.assertFalse(_spend_parcel(self.bank, h, self._dest(),
                                       [(self.bank, self.agent_kp.pk), (self.bank, cosigners[0].pk)]))
        self.assertTrue(_spend_parcel(self.bank, h, self._dest(),
                                      [(self.bank, self.agent_kp.pk),
                                       (self.bank, cosigners[0].pk), (self.bank, cosigners[1].pk)]))

    def test_time_delay_with_owner_veto_window(self):
        future = int(self.net.clock()) + 10_000
        lock = ap.time_delayed_with_veto(self.agent_kp.pk, self.owner_kp.pk, future)
        h = _fund(self.net, self.c, self.bank, lock, 100, self.usd)
        # Before the delay the agent alone cannot settle (owner's veto window).
        self.assertFalse(_spend_parcel(self.bank, h, self._dest(),
                                       [(self.bank, self.agent_kp.pk)]))
        # With the owner's consent it settles immediately.
        self.assertTrue(_spend_parcel(self.bank, h, self._dest(),
                                      [(self.bank, self.agent_kp.pk), (self.bank, self.owner_kp.pk)]))

    def test_time_delay_agent_alone_after_window(self):
        future = int(self.net.clock()) + 10_000
        lock = ap.time_delayed_with_veto(self.agent_kp.pk, self.owner_kp.pk, future)
        h = _fund(self.net, self.c, self.bank, lock, 100, self.usd)
        self.net.clock.advance(20_000)
        self.assertTrue(_spend_parcel(self.bank, h, self._dest(),
                                      [(self.bank, self.agent_kp.pk)]))

    def test_owner_claw_back_anytime(self):
        future = int(self.net.clock()) + 10_000
        lock = ap.owner_can_claw_back(self.agent_kp.pk, self.owner_kp.pk, future)
        h = _fund(self.net, self.c, self.bank, lock, 100, self.usd)
        # Owner reclaims without waiting.
        self.assertTrue(_spend_parcel(self.bank, h, self._dest(),
                                      [(self.bank, self.owner_kp.pk)]))

    def test_capped_float_shapes(self):
        locks_out = ap.capped_float(self.agent_kp.pk, self.owner_kp.pk,
                                    [(10, False), (10_000, True)])
        self.assertEqual(locks_out[0]["op"], "sig")       # small: agent alone
        self.assertEqual(locks_out[1]["op"], "all")       # large: co-signed

    def test_documented_limits_present(self):
        self.assertTrue(any("allow-list" in s for s in ap.WHAT_LOCKS_CANNOT_EXPRESS))
        self.assertTrue(any("rolling" in s or "counter" in s for s in ap.WHAT_LOCKS_CANNOT_EXPRESS))


if __name__ == "__main__":
    unittest.main()
