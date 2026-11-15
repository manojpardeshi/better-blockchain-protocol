"""Byzantine standby members of a successor committee (SPEC §5.5), over real processes.

The committee (4 members, f_k = 1) holds Byzantine members run by ``byzantine_standby.py``: they
acknowledge MIRROR without storing (``ackonly``), lie on STATUS and on ``dead`` in ``/v0/info``
(``lie``), sign any successor at once (``signany``), hand over junk and forged mirror logs in their
SUCCEED snapshots (``junksnap``), refuse ``note_release`` (``norelease``) and answer malformed
JSON now and then (``garbage``). The home's witnesses are Rust and Python; so are the new members
and the new committee of a succession.

* ``WithinBound``: one Byzantine member. Payments, rule-3 pledge releases with requests delivered
  after expiry, an equivocating owner whose first transition was acknowledged by the Byzantine
  member and only two honest ones, and a dead-man succession whose signers include the Byzantine
  member and its junk snapshot: every invariant holds, the successor inherits the binding, the
  owner's second transition never seals, and wallets pay again after the succession.
* ``BeyondBound`` (non-vacuity): two Byzantine members acknowledge without storing and sign any
  successor. The owner's first transition is acknowledged by them and one honest member, and the
  succession is signed by them and a different honest member: the successor never learns of the
  binding, the second transition seals too, and the harness reports two seals at one generation.
"""

import random
import time
import unittest

from sigil import locks, model
from sigil.server import RemoteStandby
from sigil.wallet import SealFailed, request_seal
from sigil.witness import Rejected

from .test_chaos import ChaosCase, kinds_of

ALL = "ackonly,lie,signany,junksnap,norelease,garbage"


class _Base(ChaosCase):
    def standbys(self, run):
        cid = run.cids[0]
        ks = run.c.indices(cid, role="standby")
        byz = [i for i in ks if run.c.witnesses[i]["kind"].startswith("byzk:")]
        return [run.c.url(i) for i in ks if i not in byz], [run.c.url(i) for i in byz]

    def two_spends(self, run):
        """mallory signs two transitions of one coin (an equivocating owner)."""
        m = run.mallory
        coin = next(h for h in m.holdings.values() if h["parcel"]["asset"] == run.mal_asset
                    and h["parcel"]["home"] == run.cids[0])
        reqs = []
        for k in range(2):
            a = m.address()
            header, body, tid = m.prepare([coin["ref"]], [model.parcel(a["home"], run.mal_asset,
                                          coin["parcel"]["amount"], a["lock"], a["salt"])], memo=f"t{k}")
            exp = int(time.time()) + 600
            u = locks.empty_unlock(exp)
            for pk in locks.keys_in(coin["parcel"]["lock"]) & set(m.keys):
                u["sigs"][pk] = locks.sign_unlock(m.keys[pk], coin["sigil"], tid, exp)
            p = coin["parcel"]
            reqs.append({"sigil": coin["sigil"], "header": header, "home": p["home"], "lock": p["lock"],
                         "salt": p["salt"], "unlock": u})
        return reqs

    def seal_acked_by(self, run, req, urls, tries: int = 6):
        """Collect mirror acks from ``urls`` only, then votes from every witness: a seal or None
        (retried: a ``garbage`` member answers malformed acks now and then)."""
        for _ in range(tries):
            seal = self._seal_acked_by(run, req, urls)
            if seal is not None:
                return seal
        return None

    def _seal_acked_by(self, run, req, urls):
        body = run.mallory.network.registry.latest(req["home"])
        mreq = {k: req[k] for k in ("sigil", "header", "home", "lock", "salt", "unlock")}
        mreq["version"] = body["version"]
        acks = []
        for u in urls:
            try:
                acks.append(RemoteStandby(u, 5).mirror_bind(mreq))
            except Rejected:
                pass
        r = dict(req, mirror=acks)
        votes = []
        for w in run.mallory.network.witnesses(req["home"]):
            try:
                v = w.spend(r)
            except Rejected:
                continue
            if isinstance(v, dict) and v.get("tid") == model.transition_id(req["header"]):
                votes.append(v)
        from sigil.proofs import verify_seal
        seal = model.seal_from_votes(votes) if votes else None
        return seal if seal and verify_seal(seal, run.mallory.network.registry) else None

    def succession(self, run, signers):
        """The operator drives a dead-man takeover asking only ``signers`` (all must sign)."""
        cid = run.cids[0]
        full = list(run.committees[cid])
        run.committees[cid] = list(signers)
        try:
            return run.op_succession(random.Random(5))
        finally:
            if run.committees.get(cid) == list(signers):
                run.committees[cid] = full


class WithinBound(_Base):
    def test_one_byzantine_standby_member(self):
        run = self.scenario(kinds="mixed", committee=True, dead_man=3, byz_standby=1, byz_standby_modes=ALL,
                            mallory=True)
        honest, byz = self.standbys(run)
        self.assertEqual((len(honest), len(byz)), (3, 1))
        # payments seal with acks from the honest members, whatever the Byzantine one answers
        for _ in range(3):
            self.pay_eventually(run, "alice", "bob", 2)
        # rule 3: a payment held in flight past its expiry; the lying member says "no binding",
        # the honest ones decide (they hold no binding either: the requests never got there)
        self.assertIn(run.delayed_expiry("alice", "bob", "carol", random.Random(2)), ("ok", "still-pledged"))
        # the owner's first transition is acknowledged by the Byzantine member and two honest ones
        t1, t2 = self.two_spends(run)
        self.assertIsNotNone(self.seal_acked_by(run, t1, byz + honest[:2]))
        # the succession is signed by everyone (the Byzantine member with a junk snapshot)
        self.assertEqual(self.succession(run, byz + honest), "ok")
        st = [w.status(t1["sigil"]) for w in run.mallory.network.witnesses(run.cids[0])]
        self.assertTrue(all(s["tid"] == model.transition_id(t1["header"]) for s in st), st)
        with self.assertRaises(SealFailed):
            request_seal(run.mallory.network, t2)
        self.pay_eventually(run, "alice", "bob", 1)    # the successor serves honest wallets
        self.assertEqual(self.check(run), [])


class BeyondBound(_Base):
    def test_two_byzantine_standby_members_lose_a_binding(self):
        run = self.scenario(kinds="mixed", committee=True, dead_man=3, byz_standby=2,
                            byz_standby_modes="ackonly,signany", mallory=True)
        honest, byz = self.standbys(run)
        self.assertEqual((len(honest), len(byz)), (2, 2))
        t1, t2 = self.two_spends(run)
        self.assertIsNotNone(self.seal_acked_by(run, t1, byz + honest[:1]))
        self.assertEqual(self.succession(run, byz + honest[1:]), "ok")
        seal2 = None
        for _ in range(5):
            try:
                seal2 = request_seal(run.mallory.network, t2)
                break
            except SealFailed:
                time.sleep(1)
        self.assertIsNotNone(seal2, "the successor should have lost the binding")
        found = kinds_of(self.check(run))
        self.assertIn("S1b-two-seals-one-generation", found)
        self.assertIn("S1-double-consumption", found)


if __name__ == "__main__":
    unittest.main()
