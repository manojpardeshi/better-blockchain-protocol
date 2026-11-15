"""Regressions found by review of the leftovers branch (each fails on 8a983ae)."""

import unittest

from sigil import KeyPair, Network, Wallet, model
from sigil.charter import charter_body, charter_hash
from sigil.wallet import request_seal
from sigil.witness import Rejected, Witness
from tests.test_security import manual_spend


class StandbyCarriesOwnVotes(unittest.TestCase):
    def test_reused_key_two_versions_later_does_not_equivocate(self):
        """The standby mirror carries a retired key's votes: a key re-used two versions
        later (fresh store) adopts its own vote and never votes the sibling."""
        net = Network()
        X = net.create_constellation("orion")
        mal, bob, carol = (Wallet(n, net, X) for n in ("mallory", "bob", "carol"))
        usd = mal.issue("USD", 100)
        refs, _ = mal.select(usd, 100)
        a, b = bob.address(), carol.address()
        h1, _b1, _u1, r1 = manual_spend(mal, refs, [model.parcel(X, usd, 100, a["lock"], a["salt"])])
        _h2, _b2, _u2, r2 = manual_spend(mal, refs, [model.parcel(X, usd, 100, b["lock"], b["salt"])])
        ws = net.witnesses(X)
        K = ws[0]
        s = r1[0]["sigil"]
        K.spend(r2[0])                                   # honest K votes T2
        seal = model.seal_from_votes([w.spend(r1[0]) for w in ws[1:]])
        p = mal.dossier.output(refs[0])
        proof = {"kind": "seal", "sigil": s, "gen": 0, "seal": seal,
                 "parcel": {"home": X, "lock": p["lock"], "salt": p["salt"]}}
        K.release(s, proof)
        net.rotate(X, [KeyPair.generate() for _ in range(4)], successor={"n": 4, "dead_man": 100})
        chain = net.registry.chain(X)
        cur = chain[-1]["body"]
        newk = [K.kp] + [KeyPair.generate() for _ in range(3)]
        nxt = charter_body(cur["name"], 2, [k.pk for k in newk], charter_hash(cur), None)
        sigs, snaps = {}, []
        for w in net.witnesses(X):
            sg, sn = w.freeze(nxt)
            sigs[w.pk] = sg
            snaps.append(sn)
        for m in net.committee(X):
            sg, sn = m.succeed(nxt, dict(sigs))
            sigs[m.pk] = sg
            snaps.append(sn)
        net.registry.add_chain(X, chain + [{"body": nxt, "sigs": sigs}])
        K2 = Witness(K.kp, net.registry, net.clock)
        K2.adopt(X, 2, snaps)
        self.assertTrue(K2.records[s].votes, "K's own vote reached version 2")
        with self.assertRaises(Rejected):
            K2.spend(r1[0])


class RuleThreeDuringRotation(unittest.TestCase):
    def test_unadopted_members_and_retired_votes_keep_the_pledge(self):
        net = Network()
        X = net.create_constellation("orion")
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd = alice.issue("USD", 100)
        refs, outs = alice.payment_outputs(usd, 100, bob.address())
        header, body, _tid = alice.prepare(refs, outs)
        unl = alice.authorise(header, body)
        (s, _g), = header["inputs"]
        p = alice.dossier.output(refs[0])
        request_seal(net, {"sigil": s, "header": header, "home": X, "lock": p["lock"],
                           "salt": p["salt"], "unlock": unl[s]})   # sealed; the answer is lost
        chain = net.registry.chain(X)
        cur = chain[-1]["body"]
        new = [KeyPair.generate() for _ in range(4)]
        nxt = charter_body(cur["name"], 1, [k.pk for k in new], charter_hash(cur), None)
        sigs = {}
        for w in net.witnesses(X):
            sigs[w.pk], _snap = w.freeze(nxt)
        net.registry.add_chain(X, chain + [{"body": nxt, "sigs": sigs}])
        neww = [Witness(k, net.registry, net.clock) for k in new]   # not adopted yet
        old = list(net.members[X])
        net.clock.advance(alice.pledge_ttl + alice.max_skew + 5)
        net.members[X] = old + neww
        self.assertFalse(alice.unpledge_if_unbound(s))
        with self.assertRaises(Rejected):
            neww[0].status(s)                    # a member that has not joined answers nothing
        net.members[X] = neww + old[:1]          # (b) a listed retired entry still holds the vote
        for w in neww:
            w.status = lambda sigil: {"gen": 0, "tid": None, "votes": []}
        self.assertFalse(alice.unpledge_if_unbound(s))


if __name__ == "__main__":
    unittest.main()
