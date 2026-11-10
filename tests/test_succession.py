"""Constellation succession (dead-man takeover, SPEC §5.5).

Unit tests for successor clauses and committee-signed charters, the vote gate
(mirror acks), standby members (mirror, heartbeats, the dead man, fencing,
durability), end-to-end takeovers through the in-process network and the
wallet, and adversarial scenarios: the old quorum coming back after a takeover,
a partition mistaken for death, Byzantine standby members within and beyond the
committee's fault bound, and forged succession certificates.
"""

import json
import os
import tempfile
import unittest
import urllib.error
import urllib.request
from unittest import mock

import sigil.proofs
from sigil import KeyPair, Network, Wallet, locks, model
from sigil.charter import (MAX_CHARTER_BYTES, MAX_WITNESSES, Registry, charter_body, charter_hash, constellation_id,
                           quorum, sign_charter, successor_clause, taken_over, valid_successor, verify_chain)
from sigil.gossip import GossipStore, fork_signers
from sigil.proofs import acked_by, verify_ack, verify_seal
from sigil.server import StandbyServer
from sigil.succession import MAX_MIRROR_TIDS, Standby, StandbyStore
from sigil.validate import Dossier, InvalidDossier
from sigil.wallet import SealFailed, request_seal
from sigil.witness import MAX_AUTH_BYTES, MAX_GEN, MAX_PROOF_BYTES, Conflict, Rejected, Witness

DEAD = 3600


class Home:
    """A home with a successor committee and an owner who signs anything (adversarial)."""

    def __init__(self, n=4, k=4, dead_man=DEAD, net=None, standby_cls=None):
        self.net = net or Network()
        self.owner = KeyPair.generate()
        self.ckeys = [KeyPair.generate() for _ in range(k)]
        self.X = self.net.create_constellation("home", n, successor={"keys": self.ckeys, "dead_man": dead_man})
        if standby_cls is not None:  # swap in a (Byzantine) standby class for member 0
            m = self.net.committees[self.X][0]
            b = standby_cls(m.kp, self.net.registry, self.net.clock)
            b.enter(self.X, 0, [])
            self.net.committees[self.X][0] = b
        self.exp = int(self.net.clock()) + 10 ** 6

    def parcel(self, salt):
        p = model.parcel(self.X, "x", 1, locks.sig(self.owner.pk), salt)
        return p, model.sigil_of(p)

    @staticmethod
    def hdr(inputs, tag):
        return {"inputs": [list(i) for i in inputs], "body": tag * 64}

    def req(self, h, sigil, p, home=None):
        tid = model.transition_id(h)
        u = locks.empty_unlock(self.exp)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, tid, self.exp)
        return {"sigil": sigil, "header": h, "home": home or p["home"], "lock": p["lock"], "salt": p["salt"],
                "unlock": u}

    def version(self):
        return self.net.registry.latest(self.X)["version"]

    def acks(self, req, standbys=None, version=None):
        mreq = dict(req, version=self.version() if version is None else version)
        out = []
        for m in (standbys if standbys is not None else self.net.committee(self.X)):
            try:
                out.append(m.mirror_bind(mreq))
            except Rejected:
                pass
        return out

    def votes(self, req, witnesses=None, acks=None):
        r = dict(req, mirror=self.acks(req) if acks is None else acks)
        out = []
        for w in (witnesses if witnesses is not None else self.net.witnesses(self.X)):
            try:
                out.append(w.spend(r))
            except Rejected:
                pass
        return out

    def seal(self, req, witnesses=None, acks=None):
        vs = self.votes(req, witnesses, acks)
        seal = model.seal_from_votes(vs) if vs else None
        return seal if seal and verify_seal(seal, self.net.registry) else None

    def kill_home(self):
        for w in self.net.all_witnesses(self.X):
            self.net.down.add(w.pk)

    def take_over(self, n=4, successor=None):
        self.net.clock.advance(DEAD + 1)
        self.net.probe(self.X)
        return self.net.succeed(self.X, [KeyPair.generate() for _ in range(n)], successor=successor)


def committee_chain(n=4, k=4):
    """A version-0 charter with a committee, and the keys involved."""
    ws = [KeyPair.generate() for _ in range(n)]
    ks = [KeyPair.generate() for _ in range(k)]
    body = charter_body("c", 0, [w.pk for w in ws], None, successor_clause([m.pk for m in ks], DEAD))
    return ws, ks, body, constellation_id(body)


# ------------------------------------------------------------------ charters

class CharterTests(unittest.TestCase):
    def test_successor_clause_shape(self):
        k = [KeyPair.generate().pk for _ in range(3)]
        self.assertEqual(successor_clause(k, 10), {"committee": k, "dead_man": 10})
        for bad in (([], 10), (k + k[:1], 10), (k, 0), (k, -5), (k, True), (k, 1.5), ([1, 2], 10)):
            with self.assertRaises(ValueError):
                successor_clause(*bad)
        # A body without a successor clause is hashed exactly as before the clause existed.
        b = charter_body("c", 0, k, None)
        self.assertEqual(b, {"name": "c", "version": 0, "witnesses": k, "prev": None})

    def test_version_with_committee_is_succeeded_by_committee_quorum_only(self):
        ws, ks, b0, cid = committee_chain()
        nxt = charter_body("c", 1, [KeyPair.generate().pk for _ in range(4)], charter_hash(b0))
        c0 = {"body": b0, "sigs": {}}
        def chain(signers, body=nxt):
            return [c0, {"body": body, "sigs": {k.pk: sign_charter(k, body) for k in signers}}]
        self.assertTrue(verify_chain(cid, chain(ks[:3])))             # a committee quorum
        self.assertFalse(verify_chain(cid, chain(ks[:2])))            # below quorum
        self.assertFalse(verify_chain(cid, chain(ws)))                # every member, but members are not the authority
        self.assertTrue(verify_chain(cid, chain(ws + ks[:3])))        # a cooperative rotation carries both
        forged = [c0, {"body": nxt, "sigs": {k.pk: sign_charter(k, dict(nxt, name="x")) for k in ks}}]
        self.assertFalse(verify_chain(cid, forged))                   # signatures over another body
        strangers = [KeyPair.generate() for _ in range(4)]
        self.assertFalse(verify_chain(cid, chain(strangers)))
        bad = dict(b0, successor={"committee": [], "dead_man": 5})
        self.assertFalse(verify_chain(constellation_id(bad), [{"body": bad, "sigs": {}}]))

    def test_taken_over_tells_a_takeover_from_a_cooperative_rotation(self):
        ws, ks, b0, cid = committee_chain()
        nxt = charter_body("c", 1, [KeyPair.generate().pk for _ in range(4)], charter_hash(b0))
        c0 = {"body": b0, "sigs": {}}
        coop = [c0, {"body": nxt, "sigs": {k.pk: sign_charter(k, nxt) for k in ws[:3] + ks[:3]}}]
        take = [c0, {"body": nxt, "sigs": {k.pk: sign_charter(k, nxt) for k in ks[:3]}}]
        self.assertFalse(taken_over(coop, 0))
        self.assertTrue(taken_over(take, 0))
        self.assertFalse(taken_over(take, 1))                         # no next version yet
        plain = charter_body("p", 0, [w.pk for w in ws], None)
        nxtp = charter_body("p", 1, [w.pk for w in ws], charter_hash(plain))
        self.assertFalse(taken_over([{"body": plain, "sigs": {}},
                                     {"body": nxtp, "sigs": {k.pk: sign_charter(k, nxtp) for k in ws}}], 0))

    def test_gossip_admits_successions_and_refuses_forgeries(self):
        ws, ks, b0, cid = committee_chain()
        nxt = charter_body("c", 1, [KeyPair.generate().pk for _ in range(4)], charter_hash(b0))
        c0 = {"body": b0, "sigs": {}}
        g = GossipStore()
        self.assertTrue(g.add_chain(cid, [c0]))
        self.assertFalse(g.add_chain(cid, [c0, {"body": nxt, "sigs": {k.pk: sign_charter(k, nxt) for k in ws}}]))
        self.assertTrue(g.add_chain(cid, [c0, {"body": nxt, "sigs": {k.pk: sign_charter(k, nxt) for k in ks[:3]}}]))
        # Two successors signed by overlapping committee quorums: fork evidence names the committee members.
        other = charter_body("c", 1, [KeyPair.generate().pk], charter_hash(b0))
        self.assertFalse(g.add_chain(cid, [c0, {"body": other, "sigs": {k.pk: sign_charter(k, other) for k in ks[1:]}}]))
        self.assertIn(cid, g.forks)
        self.assertEqual(fork_signers(g.forks[cid]), {ks[1].pk, ks[2].pk})


# ------------------------------------------------------------------ the vote gate

class GateTests(unittest.TestCase):
    def setUp(self):
        self.h = Home()
        self.p, self.s = self.h.parcel("aa")
        self.T = self.h.hdr([(self.s, 0)], "1")
        self.r = self.h.req(self.T, self.s, self.p)
        self.w = self.h.net.witnesses(self.h.X)[0]

    def test_a_vote_needs_acks_from_a_committee_quorum(self):
        with self.assertRaises(Rejected):
            self.w.spend(self.r)
        self.assertNotIn(self.s, self.w.records, "a refused request must not bind")
        acks = self.h.acks(self.r)
        self.assertEqual(len(acks), 4)
        self.assertTrue(all(verify_ack(a) for a in acks))
        with self.assertRaises(Rejected):
            self.w.spend(dict(self.r, mirror=acks[:2]))               # 2 of 4 < q = 3
        v = self.w.spend(dict(self.r, mirror=acks[:3]))
        self.assertEqual((v["gen"], v["tid"]), (0, model.transition_id(self.T)))
        self.assertEqual(self.w.spend(self.r), v, "returning a vote it holds needs no acks")

    def test_acks_must_match_the_binding_and_come_from_the_committee(self):
        T2 = self.h.hdr([(self.s, 0)], "2")
        other = self.h.acks(self.h.req(T2, self.s, self.p))           # another tid
        later = self.h.acks(self.h.req(self.h.hdr([(self.s, 1)], "3"), self.s, self.p))  # another gen
        p2, s2 = self.h.parcel("bb")
        foreign = self.h.acks(self.h.req(self.h.hdr([(s2, 0)], "4"), s2, p2))            # another sigil
        stranger = Standby(KeyPair.generate(), self.h.net.registry, self.h.net.clock)
        good = self.h.acks(self.r)
        forged = [dict(a, sig=good[0]["sig"]) for a in good]          # one member's signature everywhere
        for acks in (other, later, foreign, forged, good[:1] * 4, [5, "x", None, {}], "acks"):
            with self.assertRaises(Rejected):
                self.w.spend(dict(self.r, mirror=acks))
        self.assertEqual(acked_by(good + good, self.h.net.registry.committee(self.h.X, 0), self.h.X, 0,
                                  self.s, 0, model.transition_id(self.T)), {a["member"] for a in good})
        with self.assertRaises(ValueError):
            stranger.enter(self.h.X, 0, [])                           # not in the committee
        self.w.spend(dict(self.r, mirror=good))

    def test_a_home_without_committee_needs_no_acks(self):
        net = Network()
        Y = net.create_constellation("plain", 4)
        owner = KeyPair.generate()
        p = model.parcel(Y, "x", 1, locks.sig(owner.pk), "cc")
        s = model.sigil_of(p)
        h = {"inputs": [[s, 0]], "body": "5" * 64}
        exp = int(net.clock()) + 600
        u = locks.empty_unlock(exp)
        u["sigs"][owner.pk] = locks.sign_unlock(owner, s, model.transition_id(h), exp)
        net.witnesses(Y)[0].spend({"sigil": s, "header": h, "home": Y, "lock": p["lock"], "salt": p["salt"],
                                   "unlock": u})


# ------------------------------------------------------------------ standby members

class StandbyTests(unittest.TestCase):
    def setUp(self):
        self.h = Home()
        self.m = self.h.net.committees[self.h.X][0]
        self.p, self.s = self.h.parcel("aa")
        self.T = self.h.hdr([(self.s, 0)], "1")
        self.r = self.h.req(self.T, self.s, self.p)

    def nxt(self, n=4, **kw):
        cur = self.h.net.registry.latest(self.h.X)
        return charter_body(cur["name"], cur["version"] + 1, [KeyPair.generate().pk for _ in range(n)],
                            charter_hash(cur), **kw)

    def test_mirror_stores_only_owner_authorised_bindings(self):
        bad = dict(self.r, unlock=locks.empty_unlock(self.h.exp))
        for req in (dict(bad, version=0), dict(self.r, version=1), dict(self.r, version=True),
                    dict(self.r, home="elsewhere", version=0), dict(self.r), "x"):
            with self.assertRaises(Rejected):
                self.m.mirror_bind(req)
        a = self.m.mirror_bind(dict(self.r, version=0))
        self.assertTrue(verify_ack(a))
        self.assertEqual((a["sigil"], a["gen"], a["tid"]), (self.s, 0, model.transition_id(self.T)))
        self.assertEqual(self.m.mirror_bind(dict(self.r, version=0)), a)
        self.assertEqual(len(self.m.mirror[self.s]), 1, "stored once")

    def test_dead_man(self):
        nxt = self.nxt()
        with self.assertRaises(Rejected):
            self.m.succeed(nxt)                                       # just started standing by
        self.h.net.clock.advance(DEAD + 1)
        self.assertEqual(self.m.probe(self.h.net.witnesses(self.h.X)), 4)
        self.assertFalse(self.m.dead())
        with self.assertRaises(Rejected):
            self.m.succeed(nxt)                                       # every member answered
        # A wrong challenge, a forged answer, a frozen witness: none counts.
        w = self.h.net.witnesses(self.h.X)[0]
        hb = w.heartbeat("c1")
        self.assertFalse(self.m.observe(hb, "c2"))
        self.assertFalse(self.m.observe(dict(hb, witness=self.h.net.witnesses(self.h.X)[1].pk), "c1"))
        self.h.net.clock.advance(DEAD + 1)
        self.h.kill_home()
        self.h.net.probe(self.h.X)
        self.assertTrue(self.m.dead())
        sig, snap = self.m.succeed(nxt)
        self.assertEqual(snap, self.m.snapshot())
        with self.assertRaises(Rejected):
            self.m.mirror_bind(dict(self.r, version=0))               # fenced

    def test_a_minority_of_live_members_does_not_keep_a_version_alive(self):
        ws = self.h.net.witnesses(self.h.X)
        for w in ws[2:]:
            self.h.net.down.add(w.pk)
        self.h.net.clock.advance(DEAD + 1)
        self.h.net.probe(self.h.X)
        self.assertTrue(self.m.dead(), "2 of 4 cannot seal (q = 3)")
        frozen = ws[0]
        frozen.freeze(self.nxt())
        with self.assertRaises(Rejected):
            frozen.heartbeat("x")

    def test_one_successor_and_cooperative_requests(self):
        a, b = self.nxt(), self.nxt()
        ws = self.h.net.witnesses(self.h.X)
        with self.assertRaises(Rejected):
            self.m.succeed(a, {w.pk: sign_charter(w.kp, a) for w in ws[:2]})  # 2 of 4 members: not a request
        sig, _ = self.m.succeed(a, {w.pk: sign_charter(w.kp, a) for w in ws[:3]})
        self.assertEqual(self.m.succeed(a)[0], sig)                    # the same successor: answered again
        for req in (b, self.nxt()):
            with self.assertRaises(Rejected):
                self.m.succeed(req, {w.pk: sign_charter(w.kp, req) for w in ws})
        with self.assertRaises(ValueError):
            self.m.succeed(dict(a, extra=1))
        with self.assertRaises(Rejected):
            self.h.net.committees[self.h.X][1].succeed(dict(a, version=5) | {"prev": a["prev"]},
                                                       {w.pk: sign_charter(w.kp, a) for w in ws})

    def test_durable_standby(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "s.db")
            kp = KeyPair.generate()
            reg, clock = self.h.net.registry, self.h.net.clock
            # A committee member with a store, standing by for a fresh home.
            net = self.h.net
            ckeys = [kp] + [KeyPair.generate() for _ in range(3)]
            Z = net.create_constellation("z", 4, successor={"keys": ckeys, "dead_man": DEAD})
            m = Standby(kp, reg, clock, store=StandbyStore(path))
            m.enter(Z, 0, [{"q": [{"kind": "junk"}]}])
            p = model.parcel(Z, "x", 1, locks.sig(self.h.owner.pk), "dd")
            s = model.sigil_of(p)
            r = self.h.req(self.h.hdr([(s, 0)], "6"), s, p)
            a = m.mirror_bind(dict(r, version=0))
            m.store.close()
            clock.advance(DEAD * 2)
            m2 = Standby(kp, reg, clock, store=StandbyStore(path))
            self.assertEqual((m2.cid, m2.version), (Z, 0))
            self.assertEqual(m2.mirror, m.mirror)
            self.assertEqual(m2.mirror_bind(dict(r, version=0)), a)
            self.assertFalse(m2.dead(), "a restart starts a new observation window")
            clock.advance(DEAD + 1)
            self.assertTrue(m2.dead())
            cur = reg.latest(Z)
            nxt = charter_body("z", 1, [KeyPair.generate().pk], charter_hash(cur))
            sig, snap = m2.succeed(nxt)
            m2.store.close()
            m3 = Standby(kp, reg, clock, store=StandbyStore(path))
            self.assertEqual(m3.fenced_for, charter_hash(nxt))
            with self.assertRaises(Rejected):
                m3.mirror_bind(dict(r, version=0))
            with self.assertRaises(Rejected):
                m3.succeed(charter_body("z", 1, [KeyPair.generate().pk], charter_hash(cur)))
            other = StandbyStore(path)
            try:
                with self.assertRaises(ValueError):
                    Standby(KeyPair.generate(), reg, clock, store=other)
            finally:
                other.close()
            m3.store.close()


# ------------------------------------------------------------------ end to end

class SuccessionFlowTests(unittest.TestCase):
    def test_takeover_then_payments_continue_with_deep_confirmation(self):
        h = Home()
        net, X = h.net, h.X
        Y = net.create_constellation("other", 4)
        alice, bob = Wallet("alice", net, X), Wallet("bob", net, X)
        usd = alice.issue("USD", 1000)
        alice.pay(bob, usd, 300)
        h.kill_home()
        with self.assertRaises(RuntimeError):
            net.succeed(X, [KeyPair.generate() for _ in range(4)])    # too early
        self.assertEqual(h.take_over(), 1)
        chain = net.registry.chain(X)
        self.assertTrue(verify_chain(X, chain) and taken_over(chain, 0))
        carol = Wallet("carol", net, Y)
        bob.pay(carol, usd, 100)                                       # sealed by version 1
        self.assertEqual((bob.balance(usd), carol.balance(usd)), (200, 100))
        self.assertGreaterEqual(len(carol._confirmed), 2, "history sealed by v0 was deep-confirmed by v1")
        lazy = Wallet("lazy", net, Y, deep_after_succession=False)
        carol.pay(lazy, usd, 10)
        self.assertEqual(len(lazy._confirmed), 0)
        alice.pay(bob, usd, 1)                                         # alice's v0 change is spendable too

    def test_successor_inherits_every_sealed_binding(self):
        h = Home()
        p, s = h.parcel("aa")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        seal_a = h.seal(h.req(Ta, s, p))
        self.assertIsNotNone(seal_a)
        h.kill_home()
        h.take_over()
        for w in h.net.witnesses(h.X):
            self.assertEqual((w.records[s].gen, w.records[s].tid), (0, model.transition_id(Ta)))
            with self.assertRaises(Conflict):
                w.spend(dict(h.req(Tb, s, p), mirror=[]))
        self.assertIsNone(h.seal(h.req(Tb, s, p)), "a second transition at (s, 0)")
        self.assertIsNotNone(h.seal(h.req(Ta, s, p)), "re-sealing the same transition is harmless")

    def test_cooperative_rotation_of_a_version_with_committee(self):
        h = Home()
        alice, bob = Wallet("alice", h.net, h.X), Wallet("bob", h.net, h.X)
        usd = alice.issue("USD", 100)
        alice.pay(bob, usd, 40)
        old_committee = h.net.committee(h.X)
        v = h.net.rotate(h.X, [KeyPair.generate() for _ in range(4)], successor={"n": 4, "dead_man": DEAD})
        self.assertEqual(v, 1)
        chain = h.net.registry.chain(h.X)
        self.assertTrue(verify_chain(h.X, chain))
        self.assertFalse(taken_over(chain, 0), "the members froze and signed: cooperative")
        self.assertTrue(all(m.fenced_for is not None for m in old_committee))
        new = h.net.committee(h.X)
        self.assertTrue(new and all(m.version == 1 for m in new))
        bob.pay(alice, usd, 5)
        # The new committee entered standby with the handover, so a takeover of v1 keeps v0's history.
        h.kill_home()
        h.take_over()
        alice.pay(bob, usd, 1)
        bob.pay(alice, usd, 1)

    def test_rotation_of_a_version_with_committee_needs_the_committee(self):
        h = Home()
        for m in h.net.committee(h.X)[:2]:
            h.net.down.add(m.pk)
        with self.assertRaises(RuntimeError):
            h.net.rotate(h.X, [KeyPair.generate() for _ in range(4)])
        self.assertEqual(len(h.net.registry.chain(h.X)), 1)

    def test_payments_need_a_reachable_committee(self):
        h = Home()
        alice, bob = Wallet("alice", h.net, h.X), Wallet("bob", h.net, h.X)
        usd = alice.issue("USD", 10)
        for m in h.net.committee(h.X)[:2]:
            h.net.down.add(m.pk)
        with self.assertRaises(SealFailed):
            alice.pay(bob, usd, 1)                                      # L1: the committee gates votes


# ------------------------------------------------------------------ adversarial

class AckWithoutStoring(Standby):
    """A Byzantine standby member: signs acks for anything, stores nothing, hands
    over an empty mirror, and signs any successor at once."""

    def mirror_bind(self, req):
        auth = {k: req.get(k) for k in ("home", "lock", "salt", "unlock", "header")}
        from sigil.witness import authorises
        gen, tid = authorises(req["sigil"], auth)
        a = {"constellation": self.cid, "version": self.version, "member": self.pk,
             "sigil": req["sigil"], "gen": gen, "tid": tid}
        a["sig"] = self.kp.sign("mirror", model.ack_payload(a))
        return a

    def succeed(self, next_charter, sigs=None):
        return sign_charter(self.kp, next_charter), {}

    def dead(self):
        return True  # and says so when asked first (two-phase succession)


class AdversarialTests(unittest.TestCase):
    def assert_no_double_seal(self, h, sigils):
        """No (sigil, gen) has seals for two tids, counting the votes of every version."""
        votes = []
        for w in h.net.all_witnesses(h.X) + h.net.retired.get(h.X, []):
            for s in sigils:
                votes += w.status(s)["votes"]
        sealed = {}
        for v in votes:
            sealed.setdefault((v["sigil"], v["gen"], v["version"], v["tid"]), {})[v["witness"]] = v
        tids = {}
        for (s, g, ver, t), vs in sealed.items():
            if verify_seal(model.seal_from_votes(list(vs.values())), h.net.registry):
                tids.setdefault((s, g), set()).add(t)
        for k, ts in tids.items():
            self.assertEqual(len(ts), 1, f"two seals at {k}: {ts}")

    def test_old_quorum_comes_back_after_the_takeover(self):
        h = Home()
        p, s = h.parcel("aa")
        px, x = h.parcel("bb")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        Tx, Ty = h.hdr([(x, 0)], "3"), h.hdr([(x, 0)], "4")
        self.assertIsNotNone(h.seal(h.req(Ta, s, p)))
        early = h.acks(h.req(Tx, x, px))           # acks collected before the takeover, never used yet
        old = h.net.witnesses(h.X)
        h.kill_home()                               # the home is cut off: it does not answer heartbeats
        h.take_over()
        for w in old:
            h.net.down.discard(w.pk)                # ... and comes back
        # It cannot get new bindings acknowledged any more: every standby member that
        # signed the successor is fenced, and no quorum of acks exists without them.
        late = h.acks(h.req(Ty, x, px), standbys=h.net.retired_committees[h.X], version=0)
        self.assertEqual(late, [])
        for m in h.net.committees[h.X]:
            self.assertEqual(m.version, 1)
        # With acks it obtained before the fence, it can still seal Tx at (x, 0) under
        # version 0 -- and the successor inherited exactly that binding.
        seal_x = h.seal(h.req(Tx, x, px), witnesses=old, acks=early)
        self.assertIsNotNone(seal_x)
        self.assertEqual(seal_x["version"], 0)
        for w in h.net.witnesses(h.X):
            self.assertEqual(w.records[x].tid, model.transition_id(Tx))
        self.assertIsNone(h.seal(h.req(Ty, x, px)), "the successor never seals a conflicting spend")
        self.assertIsNone(h.seal(h.req(Tb, s, p), witnesses=old, acks=early))
        self.assert_no_double_seal(h, [s, x])

    def test_partition_rather_than_death(self):
        """The committee loses contact with a LIVE home for longer than the dead-man
        period and takes over. The home keeps serving clients, but can seal nothing new:
        a payment through the old version fails, through the new one succeeds."""
        h = Home()
        alice, bob = Wallet("alice", h.net, h.X), Wallet("bob", h.net, h.X)
        usd = alice.issue("USD", 100)
        old = h.net.witnesses(h.X)
        h.net.clock.advance(DEAD + 1)
        for m in h.net.committee(h.X):
            m.probe([])                              # the partition: no heartbeat gets through
        h.net.succeed(h.X, [KeyPair.generate() for _ in range(4)])
        stale = Network(h.net.clock)                 # a client that still sees version 0 only
        stale.registry.add_chain(h.X, h.net.registry.chain(h.X)[:1])
        stale.members[h.X] = old
        stale.committees[h.X] = h.net.retired_committees[h.X]
        refs, _ = alice.select(usd, 10)
        hd, bd, _ = alice.prepare(refs, [model.parcel(h.X, usd, 10, locks.sig(KeyPair.generate().pk), "ee")])
        unlocks = alice.authorise(hd, bd)
        p = alice.dossier.output(refs[0])
        req = {"sigil": hd["inputs"][0][0], "header": hd, "home": h.X, "lock": p["lock"], "salt": p["salt"],
               "unlock": unlocks[hd["inputs"][0][0]]}
        with self.assertRaises(SealFailed):
            request_seal(stale, req)                 # fenced standby members acknowledge nothing
        seal = request_seal(h.net, req)              # the successor seals it
        self.assertEqual(seal["version"], 1)

    def test_byzantine_standby_member_within_the_bound(self):
        h = Home(standby_cls=AckWithoutStoring)
        byz, honest = h.net.committees[h.X][0], h.net.committees[h.X][1:]
        p, s = h.parcel("aa")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        r = h.req(Ta, s, p)
        acks = h.acks(r, standbys=[byz] + honest[:2])      # the Byzantine member and two honest ones
        self.assertIsNotNone(h.seal(r, acks=acks))
        self.assertNotIn(s, byz.mirror)
        h.kill_home()
        # It signs at once; the honest members refuse while the dead-man period runs.
        cur = h.net.registry.latest(h.X)
        with self.assertRaises(RuntimeError):
            h.net.succeed(h.X, [KeyPair.generate() for _ in range(4)])
        # The takeover is signed by the Byzantine member (empty snapshot), honest[1] (which
        # stored Ta) and honest[2] (which never saw it): the vote's ack quorum and the
        # signing quorum still share honest[1], whose log hands Ta over.
        h.net.down.add(honest[0].pk)
        h.take_over()
        for w in h.net.witnesses(h.X):
            self.assertEqual(w.records[s].tid, model.transition_id(Ta))
        self.assertIsNone(h.seal(h.req(Tb, s, p)))
        self.assert_no_double_seal(h, [s])

    def test_committee_beyond_its_fault_bound_can_double_spend(self):
        """The accepted failure mode: a committee with more than f Byzantine members
        signs a succession with empty evidence, and an owner who colludes double-spends
        (exactly what a corrupt quorum of a version can do). Holders' trust in a home
        includes its committees (SPEC §5.5)."""
        net = Network()
        h = Home(net=net)
        for i in range(3):                           # 3 of 4 standby members corrupt: beyond f = 1
            m = net.committees[h.X][i]
            b = AckWithoutStoring(m.kp, net.registry, net.clock)
            b.enter(h.X, 0, [])
            net.committees[h.X][i] = b
        p, s = h.parcel("aa")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        self.assertIsNotNone(h.seal(h.req(Ta, s, p)))
        net.down.add(net.committees[h.X][3].pk)      # the honest one is left out
        net.succeed(h.X, [KeyPair.generate() for _ in range(4)])
        self.assertIsNotNone(h.seal(h.req(Tb, s, p)), "beyond the bound, safety is lost")

    def test_forged_succession_certificate_is_refused_by_holders(self):
        h = Home()
        alice = Wallet("alice", h.net, h.X)
        usd = alice.issue("USD", 10)
        bob = Wallet("bob", h.net, h.X)
        alice.pay(bob, usd, 10)
        # Mallory forges version 1 of the home with her own keys (not the committee's),
        # and seals a spend of bob's coin with them.
        cur = h.net.registry.latest(h.X)
        mk = [KeyPair.generate() for _ in range(4)]
        forged = charter_body(cur["name"], 1, [k.pk for k in mk], charter_hash(cur))
        chain = h.net.registry.chain(h.X) + [{"body": forged, "sigs": {k.pk: sign_charter(k, forged) for k in mk}}]
        self.assertFalse(verify_chain(h.X, chain))
        # Old members (a quorum of them) signing it are not the authority either.
        olds = h.net.witnesses(h.X)
        chain2 = h.net.registry.chain(h.X) + [{"body": forged,
                                                "sigs": {w.pk: sign_charter(w.kp, forged) for w in olds}}]
        self.assertFalse(verify_chain(h.X, chain2))
        d = Dossier()
        d.merge(bob.dossier)
        d.charters[h.X] = chain2
        carol = Wallet("carol", Network(), None, trusted={h.X})
        carol.network.registry.add_chain(h.X, h.net.registry.chain(h.X))
        with self.assertRaises(InvalidDossier):
            carol.verifier.verify_parcel(d, next(iter(bob.holdings.values()))["ref"])

    def test_live_home_is_never_taken_over(self):
        h = Home()
        for _ in range(10):
            h.net.clock.advance(DEAD // 2)
            h.net.probe(h.X)                         # heartbeats keep coming
            with self.assertRaises(RuntimeError):
                h.net.succeed(h.X, [KeyPair.generate() for _ in range(4)])

    def test_reused_key_brings_its_votes_across_a_takeover(self):
        h = Home()
        p, s = h.parcel("aa")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        w0 = h.net.witnesses(h.X)[0]
        h.votes(h.req(Ta, s, p), witnesses=[w0])     # w0 votes Ta alone (unsealed)
        h.kill_home()
        h.net.clock.advance(DEAD + 1)
        h.net.probe(h.X)
        h.net.succeed(h.X, [w0.kp] + [KeyPair.generate() for _ in range(3)])
        h.net.down.discard(w0.pk)                    # its operator runs the key again, in version 1
        w0b = next(w for w in h.net.witnesses(h.X) if w.pk == w0.pk)
        self.assertEqual(w0b.version, 1)
        with self.assertRaises(Rejected):
            w0b.spend(dict(h.req(Tb, s, p), mirror=[]))
        votes = w0b.status(s)["votes"]
        self.assertEqual({v["tid"] for v in votes if v["gen"] == 0}, {model.transition_id(Ta)})


class MoreAdversarialTests(unittest.TestCase):
    """Byzantine members of the successor version and of the committee, forged acks
    and forged requests."""

    assert_no_double_seal = AdversarialTests.assert_no_double_seal

    def test_byzantine_member_of_the_successor_version(self):
        h = Home()
        p, s = h.parcel("aa")
        px, x = h.parcel("bb")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        self.assertIsNotNone(h.seal(h.req(Ta, s, p)))
        h.kill_home()
        h.take_over()
        byz = h.net.witnesses(h.X)[0]                # one of the four new members turns Byzantine (f = 1)
        honest = h.net.witnesses(h.X)[1:]
        tb = model.transition_id(Tb)
        forged = {"constellation": h.X, "version": 1, "witness": byz.pk, "sigil": s, "gen": 0, "tid": tb,
                  "time": int(h.net.clock())}
        forged["sig"] = byz.kp.sign("vote", model.vote_payload(forged))
        votes = [forged] + h.votes(h.req(Tb, s, p), witnesses=honest)
        self.assertEqual(len(votes), 1, "the honest members inherited Ta and refuse Tb")
        self.assertFalse(verify_seal(model.seal_from_votes(votes), h.net.registry))
        # Nor can it kill Ta: one version's votes against Ta need a quorum.
        dp = {"kind": "votes", "sigil": s, "gen": 0, "parcel": {k: p[k] for k in ("home", "lock", "salt")},
              "votes": [forged]}
        for w in honest:
            with self.assertRaises(Rejected):
                w.release(s, dp)
        # Everything else keeps working through the honest members: x is spent once.
        self.assertIsNotNone(h.seal(h.req(h.hdr([(x, 0)], "3"), x, px), witnesses=honest))
        self.assert_no_double_seal(h, [s, x])

    def test_byzantine_committee_member_forges_its_handover_and_signs_twice(self):
        """A Byzantine standby member hands over junk, unverifiable bindings, releases
        without a valid death proof and the owner's second (unsealed) transition, and
        signs a second successor. ADOPT ignores what does not verify, the equivocation
        only makes the record contested, and the second successor never gets a quorum."""
        class Forger(Standby):
            junk = None

            def succeed(self, next_charter, sigs=None):
                return sign_charter(self.kp, next_charter), self.junk

        h = Home(standby_cls=Forger)
        byz = h.net.committees[h.X][0]
        p, s = h.parcel("aa")
        Ta, Tb, Tc = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2"), h.hdr([(s, 0)], "3")
        ra = h.req(Ta, s, p)
        self.assertIsNotNone(h.seal(ra))
        rb = h.req(Tb, s, p)                         # the owner also authorised Tb (never sealed)
        auth_b = {k: rb[k] for k in ("home", "lock", "salt", "unlock", "header")}
        bad_auth = dict(auth_b, header=Tc)           # Tc: no owner signature for it
        dead_claim = {"kind": "release", "gen": 0, "tid": model.transition_id(Ta), "header": Ta,
                      "proof": {"kind": "votes", "sigil": s, "gen": 0, "parcel": {}, "votes": []}}
        byz.junk = {s: [{"kind": "bind", "gen": 0, "auth": bad_auth}, dead_claim, {"kind": "bind", "gen": 0, "auth": auth_b},
                        "not an entry", {"kind": "seal", "seal": {"tid": "x"}}] + [{"kind": "noise", "i": i} for i in range(50)],
                    "elsewhere": "not a log"}
        h.kill_home()
        h.take_over()
        tids = {model.transition_id(Ta), model.transition_id(Tb)}
        for w in h.net.witnesses(h.X):
            r = w.records[s]
            self.assertEqual(r.tid, "!contested", "Ta is alive and Tb is the owner's own sibling")
            self.assertEqual({c[1] for c in r.candidates}, tids)
        self.assertIsNone(h.seal(h.req(Tb, s, p)))
        self.assertIsNone(h.seal(h.req(Tc, s, p)))
        # A second successor of version 0: the Byzantine member signs it, no honest one does.
        cur = h.net.registry.chain(h.X)[0]["body"]
        other = charter_body(cur["name"], 1, [KeyPair.generate().pk for _ in range(4)], charter_hash(cur))
        sigs = {byz.pk: byz.succeed(other)[0]}
        for m in h.net.retired_committees[h.X][1:]:
            with self.assertRaises(Rejected):
                m.succeed(other)
        self.assertFalse(verify_chain(h.X, h.net.registry.chain(h.X)[:1] + [{"body": other, "sigs": sigs}]))
        self.assert_no_double_seal(h, [s])

    def test_forged_and_replayed_acks_do_not_open_the_gate(self):
        h = Home()
        p, s = h.parcel("aa")
        Ta, Tb = h.hdr([(s, 0)], "1"), h.hdr([(s, 0)], "2")
        ra, rb = h.req(Ta, s, p), h.req(Tb, s, p)
        good_a = h.acks(ra)
        outsiders = [KeyPair.generate() for _ in range(4)]

        def ack(kp, **kw):
            a = {"constellation": h.X, "version": 0, "member": kp.pk, "sigil": s, "gen": 0,
                 "tid": model.transition_id(Tb)} | kw
            a["sig"] = kp.sign("mirror", model.ack_payload(a))
            return a

        cases = {
            "keys outside the committee": [ack(k) for k in outsiders],
            "acks for another transition": good_a,
            "acks for another version": [ack(m.kp, version=1) for m in h.net.committee(h.X)],
            "a version that is not an integer": [ack(m.kp, version=True) for m in h.net.committee(h.X)],
            "bad signatures": [dict(a, tid=model.transition_id(Tb)) for a in good_a],
            "one member many times": [h.acks(rb)[0]] * 4,
        }
        w = h.net.witnesses(h.X)[0]
        for name, acks in cases.items():
            with self.assertRaises(Rejected, msg=name):
                w.spend(dict(rb, mirror=acks))
            self.assertNotIn(s, w.records, name)        # nothing is persisted on refusal
        self.assertTrue(w.spend(dict(rb, mirror=h.acks(rb))))

    def test_a_witness_without_its_own_charter_votes_on_nothing(self):
        """A member of a version with a committee restarted with a registry older than
        its store cannot tell whether acks are needed: it fails closed (it used to vote
        without acks, breaking mirror before vote)."""
        h = Home()
        h.net.rotate(h.X, [KeyPair.generate() for _ in range(4)], successor={"n": 4, "dead_man": DEAD})
        w = h.net.witnesses(h.X)[0]
        stale = Registry()
        stale.add_chain(h.X, h.net.registry.chain(h.X)[:1])
        w.registry = stale
        p, s = h.parcel("aa")
        r = h.req(h.hdr([(s, 0)], "1"), s, p)
        with self.assertRaisesRegex(Rejected, "own charter version unknown"):
            w.spend(dict(r, mirror=[]))
        self.assertNotIn(s, w.records)
        m = h.net.committees[h.X][0]
        m.registry = stale
        self.assertFalse(m.dead())
        with self.assertRaisesRegex(Rejected, "own charter version unknown"):
            m.succeed(h.net.registry.latest(h.X))
        w.registry = h.net.registry                  # the operator updates the registry file
        self.assertEqual(w.spend(dict(r, mirror=h.acks(r)))["version"], 1)

    def test_forged_cooperative_request_is_not_a_request(self):
        h = Home()
        m = h.net.committees[h.X][0]
        cur = h.net.registry.latest(h.X)
        nxt = charter_body(cur["name"], 1, [KeyPair.generate().pk for _ in range(4)], charter_hash(cur))
        ws = h.net.witnesses(h.X)
        fakes = [KeyPair.generate() for _ in range(4)]
        for sigs in ({k.pk: sign_charter(k, nxt) for k in fakes},                       # not members
                     {w.pk: sign_charter(fakes[0], nxt) for w in ws},                     # members' keys, forged
                     {w.pk: sign_charter(w.kp, dict(nxt, name="other")) for w in ws}):    # signed another body
            with self.assertRaises(Rejected):
                m.succeed(nxt, sigs)
        self.assertIsNone(m.fenced_for)


class SuccessionLimitTests(unittest.TestCase):
    """The resource bounds of the main line, applied to succession (SPEC §5.5): what one
    request can make a standby member store, the handover kept as a set, one signature
    check per committee member for acks, and the committee cap."""

    def setUp(self):
        self.h = Home()
        self.m = self.h.net.committees[self.h.X][0]
        self.p, self.s = self.h.parcel("aa")

    def mreq(self, hdr):
        return dict(self.h.req(hdr, self.s, self.p), version=0)

    def test_mirror_bounds_what_one_request_stores(self):
        big = self.h.hdr([(self.s, 0)], "1") | {"pad": "x" * MAX_AUTH_BYTES}
        with self.assertRaisesRegex(Rejected, "authorisation too large"):
            self.m.mirror_bind(self.mreq(big))
        with self.assertRaisesRegex(Rejected, "generation limit"):
            self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, MAX_GEN)], "1")))
        self.assertEqual(self.m.mirror, {}, "nothing stored")
        self.assertTrue(verify_ack(self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, MAX_GEN - 1)], "1")))))
        first = self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, 0)], "0")))
        for i in range(1, MAX_MIRROR_TIDS):
            self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, 0)], str(i))))
        with self.assertRaisesRegex(Rejected, "too many transitions"):
            self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, 0)], "9")))
        self.assertEqual(self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, 0)], "0"))), first,
                         "a stored binding is acknowledged again")
        self.m.mirror_bind(self.mreq(self.h.hdr([(self.s, 1)], "9")))   # another generation is fine
        self.assertEqual(len(self.m.mirror[self.s]), MAX_MIRROR_TIDS + 2)

    def test_release_entries_only_for_mirrored_bindings_and_bounded_proofs(self):
        h, m = self.h, self.m
        px, x = h.parcel("bb")
        T, T2, Ty = h.hdr([(self.s, 0), (x, 0)], "1"), h.hdr([(self.s, 0), (x, 0)], "2"), h.hdr([(x, 0)], "3")
        seal_y = h.seal(h.req(Ty, x, px))
        dp = {"kind": "seal", "sigil": x, "gen": 0, "parcel": {k: px[k] for k in ("home", "lock", "salt")},
              "seal": seal_y}

        def entry(hdr, proof=dp):
            return {"kind": "release", "gen": 0, "tid": model.transition_id(hdr), "header": hdr, "proof": proof}

        with self.assertRaises(Rejected):
            m.note_release(self.s, entry(T))          # T was never mirrored here
        m.mirror_bind(self.mreq(T))
        with self.assertRaisesRegex(Rejected, "death proof too large"):
            m.note_release(self.s, entry(T, dict(dp, pad="x" * MAX_PROOF_BYTES)))
        self.assertTrue(m.note_release(self.s, entry(T)))
        self.assertFalse(m.note_release(self.s, entry(T)), "stored once")
        with self.assertRaises(Rejected):
            m.note_release(self.s, entry(T2))         # anyone can build T2; it was never bound here
        self.assertEqual([e["kind"] for e in m.mirror[self.s]], ["bind", "release"])

    def test_handover_keeps_each_entry_once_and_every_distinct_one(self):
        h = self.h
        r = h.req(h.hdr([(self.s, 0)], "1"), self.s, self.p)
        bind = {"kind": "bind", "gen": 0, "auth": {k: r[k] for k in ("home", "lock", "salt", "unlock", "header")}}
        junk = [{"kind": "bind", "gen": i, "auth": None} for i in range(3)]
        snap = {self.s: [bind] + junk, "x": "not a log"}
        fresh = Standby(h.ckeys[1], h.net.registry, h.net.clock)
        fresh.enter(h.X, 0, [snap, snap, snap, "not a snapshot"])
        self.assertEqual(fresh.mirror[self.s], [bind] + junk)
        self.assertEqual(fresh.mirrored, {(self.s, 0, model.transition_id(r["header"]))})
        self.assertNotIn("x", fresh.mirror)

    def test_one_signature_check_per_committee_member(self):
        h = self.h
        r = h.req(h.hdr([(self.s, 0)], "1"), self.s, self.p)
        good = h.acks(r)
        forged = [dict(a, sig=good[(i + 1) % len(good)]["sig"]) for i, a in enumerate(good)]
        acks = [f for f in forged for _ in range(3)] + good    # 3 forgeries per member, then the real ack
        committee = [m.pk for m in h.net.committee(h.X)]
        tid = model.transition_id(r["header"])
        real = sigil.proofs.verify_ack
        with mock.patch.object(sigil.proofs, "verify_ack", side_effect=real) as spy:
            got = acked_by(acks, committee, h.X, 0, self.s, 0, tid)
        self.assertEqual(spy.call_count, len(committee))
        self.assertEqual(got, set(), "each member's first ack is the one that counts")
        self.assertEqual(acked_by(good + forged, committee, h.X, 0, self.s, 0, tid), set(committee))
        with self.assertRaises(Rejected):
            h.net.witnesses(h.X)[0].spend(dict(r, mirror=acks))

    def test_committee_cap_and_oversized_successor(self):
        keys = ["%064x" % i for i in range(MAX_WITNESSES + 1)]
        self.assertTrue(valid_successor({"committee": keys[:MAX_WITNESSES], "dead_man": 1}))
        self.assertFalse(valid_successor({"committee": keys, "dead_man": 1}))
        with self.assertRaises(ValueError):
            successor_clause(keys, 1)
        ws = [KeyPair.generate() for _ in range(4)]
        body = charter_body("c", 0, [w.pk for w in ws], None)
        body["successor"] = {"committee": keys, "dead_man": 1}
        self.assertFalse(verify_chain(constellation_id(body), [{"body": body, "sigs": {}}]))
        cur = self.h.net.registry.latest(self.h.X)
        huge = charter_body("n" * MAX_CHARTER_BYTES, 1, [KeyPair.generate().pk], charter_hash(cur))
        self.h.net.clock.advance(DEAD + 1)
        self.h.kill_home()
        self.h.net.probe(self.h.X)
        with self.assertRaisesRegex(Rejected, "charter too large"):
            self.m.succeed(huge)
        self.assertIsNone(self.m.fenced_for, "never fenced for a charter that can never be valid")

    def test_standby_server_admission_control(self):
        srv = StandbyServer(self.m, "127.0.0.1", 0, admin_token="tok", rate_limit=0.001, rate_burst=1).start()
        try:
            def post(method, body, token=None):
                headers = {"Content-Type": "application/json"}
                if token:
                    headers["Authorization"] = f"Bearer {token}"
                req = urllib.request.Request(f"{srv.url}/v0/{method}", data=json.dumps(body).encode(),
                                             headers=headers, method="POST")
                try:
                    with urllib.request.urlopen(req, timeout=5) as resp:
                        return resp.status
                except urllib.error.HTTPError as e:
                    return e.code
            req = self.mreq(self.h.hdr([(self.s, 0)], "1"))
            self.assertEqual(post("mirror", {"request": req}), 200)
            self.assertEqual(post("mirror", {"request": req}), 429)
            for _ in range(3):                        # operator calls are never limited
                self.assertEqual(post("probe", {"urls": []}, token="tok"), 200)
        finally:
            srv.stop()


if __name__ == "__main__":
    unittest.main()
