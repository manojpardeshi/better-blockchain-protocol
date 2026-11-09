"""Scenario 4: recovery with a death proof after the counter-party double-spends.

alice's input is sealed to a swap whose other input mallory spends elsewhere.
alice's wallet is restarted from its directory, finds the death proof, has every
witness of her home (Rust and Python) release her input, and spends it again.
"""

import unittest

from sigil import model, wallet_store
from sigil.wallet import SealFailed, Wallet, find_death_proof, request_seal
from sigil.swap import propose_swap
from sigil.witness import Rejected
from tests.integration.harness import MIXED, IntegrationCase, manual_spend


class RecoveryTests(IntegrationCase):
    def test_abort_with_death_proof_after_counterparty_double_spend(self):
        c = self.c
        # Both constellations exist before any witness starts, so each knows the other's charter
        # (see test_abort_when_home_does_not_know_the_counterparty_home for the other case).
        X, xi = c.constellation("orion", MIXED, start=False)
        Y, yi = c.constellation("lyra", ["rust", "rust", "python", "python"], start=False)
        c.start_all(xi + yi)
        directory = c.directory()
        net = self.net(directory)
        adir = self.wpath("alice")
        alice = Wallet("alice", net, X, on_pledge=lambda w: wallet_store.save(w, adir))
        mallory = Wallet("mallory", net, Y)
        bob = Wallet("bob", net, Y, deep_threshold=1)
        usd, gold = alice.issue("USD", 100), mallory.issue("GOLD", 10)
        wallet_store.save(alice, adir)

        header, body, _ = propose_swap(alice, usd, 100, mallory, gold, 10)
        tid = model.transition_id(header)
        unlocks = {**alice.authorise(header, body), **mallory.authorise(header, body)}
        a_main, m_main = header["inputs"][0][0], header["inputs"][1][0]
        # mallory spends her swap input elsewhere first, and seals it.
        me = mallory.address()
        hb, bb, ub, betrayal = manual_spend(mallory, [body["inputs"][1]],
                                            [model.parcel(Y, gold, 10, me["lock"], me["salt"])])
        mallory.dossier.add_seal(request_seal(net, betrayal[0]))
        mallory.finalise(hb, bb, ub)
        # alice seals her own input to the swap, then cannot get mallory's.
        with self.assertRaises(SealFailed):
            alice.seal(header, body, unlocks)
        for w in net.witnesses(X):
            self.assertEqual(w.status(a_main)["tid"], tid, w)
        del alice

        # alice's wallet process restarts: the pending swap and its pledge were saved.
        alice = wallet_store.load(adir, self.net(directory))
        self.assertIn(tid, alice.pending)
        self.assertEqual(alice.pledged[a_main][:2], (0, tid))
        with self.assertRaises(ValueError):          # still pledged: she will not sign another spend
            alice.pay(bob, usd, 100)
        self.assertEqual(alice.abort(alice.pending[tid]["header"]), [a_main])
        wallet_store.save(alice, adir)
        for w in alice.network.witnesses(X):
            st = w.status(a_main)
            self.assertEqual((st["gen"], st["tid"]), (1, None), w)
            with self.assertRaises(Rejected):        # the proof cannot release anything twice
                w.release(a_main, find_death_proof(alice.network, header, tid, alice._parcels_for(header)))
        # The swap can never be sealed now: mallory's input is consumed elsewhere.
        with self.assertRaises(SealFailed) as e:
            request_seal(net, {"sigil": m_main, "header": header, "home": Y,
                               "lock": mallory.dossier.output(body["inputs"][1])["lock"],
                               "salt": mallory.dossier.output(body["inputs"][1])["salt"], "unlock": unlocks[m_main]})
        self.assertEqual(len(e.exception.conflicts), 4)

        # alice spends her input again, at generation 1, after another restart.
        alice = wallet_store.load(adir, self.net(directory))
        alice.on_pledge = lambda w: wallet_store.save(w, adir)
        alice.pay(bob, usd, 60)
        wallet_store.save(alice, adir)
        self.assertEqual((alice.balance(usd), bob.balance(usd)), (40, 60))
        self.assertTrue(any(s == a_main and g == 1 for s, g, _t in bob._confirmed))
        self.check_invariants({"alice": wallet_store.load(adir, self.net(directory)), "mallory": mallory, "bob": bob},
                              headers=[header])

    def test_abort_when_home_does_not_know_the_counterparty_home(self):
        """BUG (wallet, high: funds stuck, no safety loss): ``Wallet.abort`` reports an input
        released when no witness released it.

        Scenario: alice's home X was started before mallory's home Y existed, so X's witnesses
        have never seen Y's charter (constellations are permissionless and appear over time;
        witnesses learn charters only from their registry file or gossip). alice's input is
        sealed to a swap; mallory spends her own swap input elsewhere at Y. alice calls
        ``abort``: ``find_death_proof`` builds a valid seal-kind death proof from Y's votes,
        but every X witness (Rust and Python alike) answers RELEASE with "invalid death proof",
        because it cannot verify a seal of a constellation it does not know.

        Impact: ``abort`` swallows every ``Rejected`` from RELEASE ("it accepts g + 1 anyway"),
        sets the holding's generation to 1, deletes the pledge and drops the pending swap. The
        witnesses are still bound at generation 0, so every later spend of the input is refused
        ("bound at an earlier generation; release it first"), and the wallet no longer has the
        pledge or header it would need to retry the abort. The parcel is stuck until someone
        re-runs RELEASE by hand.

        Suggested fix: before RELEASE, gossip the chain of the evidence's constellation (the
        death proof's ``parcel.home`` and seal/votes constellation) to the home's witnesses
        (``/v0/gossip``, as ``RemoteNetwork._install`` does); and in ``abort``, keep the pledge
        and the pending transition unless at least a quorum of the home's current members
        either released or report the sigil unbound at ``g``/past ``g`` (STATUS), raising
        otherwise.
        """
        c = self.c
        X, _ = c.constellation("orion", MIXED)                          # started before Y exists
        Y, _ = c.constellation("lyra", ["rust", "rust", "python", "python"])
        net = self.net()
        alice, mallory = Wallet("alice", net, X), Wallet("mallory", net, Y)
        usd, gold = alice.issue("USD", 100), mallory.issue("GOLD", 10)
        header, body, _ = propose_swap(alice, usd, 100, mallory, gold, 10)
        unlocks = {**alice.authorise(header, body), **mallory.authorise(header, body)}
        me = mallory.address()
        *_, betrayal = manual_spend(mallory, [body["inputs"][1]], [model.parcel(Y, gold, 10, me["lock"], me["salt"])])
        request_seal(net, betrayal[0])
        with self.assertRaises(SealFailed):
            alice.seal(header, body, unlocks)
        a_main = header["inputs"][0][0]
        self.assertEqual(alice.abort(header), [a_main])                # reported as released ...
        for w in net.witnesses(X):                                      # ... but is it?
            st = w.status(a_main)
            self.assertEqual((st["gen"], st["tid"]), (1, None), w)
