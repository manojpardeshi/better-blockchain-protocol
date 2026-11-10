"""Scenario 9: a rotation and an equivocation proof spread through mixed witnesses to a wallet.

Witnesses never talk to each other; clients run the anti-entropy rounds
(``sigil.gossip.gossip_round``). The facts start at witnesses the wallet cannot
reach, cross a relay constellation H (Rust and Python) that knew nothing about
them, and reach the wallet, which then refuses seals that need the convicted
witness's vote.
"""

import signal

from sigil import model
from sigil.gossip import GossipStore, gossip_round
from sigil.validate import InvalidDossier
from sigil.wallet import Wallet, request_seal
from sigil.witnessd import load_key
from tests.integration.harness import MIXED, IntegrationCase


class GossipTests(IntegrationCase):
    def test_rotation_and_equivocation_proof_reach_a_wallet(self):
        c = self.c
        # H starts first: its witnesses know no other constellation.
        H, h_idx = c.constellation("haven", ["rust", "python", "python", "rust"])
        G, g_idx = c.constellation("guilty", MIXED)
        R, r_old = c.constellation("rotor", ["python", "rust", "python", "rust"])
        h_urls, g_urls = c.urls(h_idx), c.urls(g_idx)

        # A real payment in G, then G's witness 0 (a Rust process) signs a second vote for the
        # same sigil and generation: an equivocation proof against it.
        net_g = self.net({G: g_urls})
        alice, bob = Wallet("alice", net_g, G), Wallet("bob", net_g, G)
        usd = alice.issue("USD", 100)
        tid = alice.pay(bob, usd, 10)
        seal = next(s for s in alice.dossier.seals.values() if s["tid"] == tid)
        g0 = load_key(c.witnesses[g_idx[0]]["key"])
        real = next(v for v in model.votes_of_seal(seal) if v["witness"] == g0.pk)
        forged = dict(real, tid="ee" * 32)
        forged["sig"] = g0.sign("vote", model.vote_payload(forged))
        proof = {"a": real, "b": forged}

        # The operator rotates R; only R's members (old and new) know version 1.
        new = c.add_members(R, ["rust", "python", "rust", "python"], c.admin())
        c.start_all(new)
        for i in new:
            c.witnesses[i]["pending"] = False
        operator = self.net({R: c.urls(r_old)})
        self.assertEqual(operator.rotate(R, c.urls(new), c.token), 1)
        r_new = operator.witnesses(R)
        # The proof is told to one new member of R (a Python process), which knows G's charter.
        self.assertEqual(r_new[1].gossip({"proofs": [proof]})["proofs"], 1)

        # dave's wallet can reach only H and G. Before any gossip, it knows nothing of either fact.
        dave = Wallet("dave", self.net({H: h_urls, G: g_urls}), H)
        self.assertEqual(len(dave.network.registry.chain(R)), 0)
        store = GossipStore(dave.network.registry)
        self.assertEqual(gossip_round(dave.network, store)["learned"]["proofs"], 0)

        # A relay client that reaches R's new members and H runs a round: H's Rust and Python
        # witnesses learn R's chain (version 1) and the proof against G's witness.
        relay = GossipStore(operator.registry)
        relay_net = self.net({R: c.urls(new), H: h_urls})
        relay_net.registry = operator.registry
        out = gossip_round(relay_net, relay)
        self.assertEqual(out["peers"], 8)
        for w in self.net({H: h_urls}).witnesses(H):
            self.assertEqual(len(w.charters()[R]), 2, w)
            self.assertEqual([p["a"]["witness"] for p in w.proofs()["proofs"]], [g0.pk], w)

        # dave's next round brings both facts to his wallet, which convicts the witness.
        out = gossip_round(dave.network, store)
        self.assertEqual((out["learned"]["proofs"], out["learned"]["charters"] >= 1), (1, True))
        self.assertEqual(len(dave.network.registry.chain(R)), 2)
        self.assertEqual(store.apply(dave.policy), 1)
        self.assertEqual(dave.policy.convicted, {g0.pk})
        dave.trust(G)
        # G's witness 3 is down; alice's payment to dave is sealed by witnesses 0, 1 and 2: a valid
        # seal for alice, who has not heard of the proof, but not for dave.
        c.kill(g_idx[3], signal.SIGKILL)
        refs, outputs = alice.payment_outputs(usd, 20, dave.address(G))
        tid2 = alice.transact(refs, outputs)
        with self.assertRaises(InvalidDossier):
            dave.receive(alice.dossier.ancestry([tid2]), [model.ref(tid2, 0)])
        self.assertEqual(dave.balance(usd), 0)
        # Once witness 3 is back, alice gathers a seal with a quorum of honest votes; dave accepts.
        c.restart(g_idx[3])
        tx = alice.dossier.transitions[tid2]
        (s, _g), = tx["header"]["inputs"]
        p = alice.dossier.output(tx["body"]["inputs"][0])
        better = request_seal(alice.network, {"sigil": s, "header": tx["header"], "home": G, "lock": p["lock"],
                                              "salt": p["salt"], "unlock": tx["unlocks"][s]})
        self.assertEqual(len(better["votes"]), 4)
        alice.dossier.add_seal(better)
        dave.receive(alice.dossier.ancestry([tid2]), [model.ref(tid2, 0)])
        self.assertEqual((alice.balance(usd), bob.balance(usd), dave.balance(usd)), (70, 10, 20))
        # A further round has nothing new to say.
        self.assertEqual(gossip_round(dave.network, store)["learned"], {"charters": 0, "proofs": 0, "forks": 0})
        self.check_invariants({"alice": alice, "bob": bob, "dave": dave})
