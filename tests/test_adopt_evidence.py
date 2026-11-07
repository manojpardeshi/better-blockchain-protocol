"""ADOPT keeps only verifiable evidence that bears on a binding (SPEC 5.4).

A Byzantine member of a freezing quorum can hand over anything in its
snapshot. Before, every entry it sent was stored in the new record's log and
forwarded at every later rotation; now only bind entries with a valid
authorisation, and release and seal entries that verify for a transaction
bound in the evidence, are kept.
"""

import unittest

from sigil import KeyPair, Network, locks, model
from sigil.charter import charter_body, charter_hash
from sigil.witness import Witness


class AdoptEvidenceFilterTests(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion", 4)
        self.owner = KeyPair.generate()
        self.exp = int(self.net.clock()) + 10 ** 9

        def mk(salt):
            p = model.parcel(self.X, "x", 1, locks.sig(self.owner.pk), salt)
            return p, model.sigil_of(p)

        self.ps, self.s = mk("s")
        self.px, self.x = mk("x")

    def hdr(self, inputs, tag):
        return {"inputs": [list(i) for i in inputs], "body": tag * 64}

    def req(self, h, sigil, p):
        u = locks.empty_unlock(self.exp)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, sigil, model.transition_id(h), self.exp)
        return {"sigil": sigil, "header": h, "home": self.X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def tgt(self, p):
        return {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}

    def rotate_with(self, extra_snapshot):
        """Freeze version 0 and adopt version 1 at a fresh key, adding ``extra_snapshot``."""
        cur = self.net.registry.latest(self.X)
        kp = KeyPair.generate()
        nxt = charter_body(cur["name"], cur["version"] + 1, [kp.pk], charter_hash(cur))
        sigs, snaps = {}, []
        for w in self.net.witnesses(self.X)[:3]:
            sig, snap = w.freeze(nxt)
            sigs[w.pk] = sig
            snaps.append(snap)
        self.net.registry.add_chain(self.X, self.net.registry.chain(self.X) + [{"body": nxt, "sigs": sigs}])
        a = Witness(kp, self.net.registry, self.net.clock)
        a.adopt(self.X, nxt["version"], snaps + [extra_snapshot])
        return a, snaps

    def test_only_verifiable_entries_about_bindings_are_kept(self):
        k = self.net.witnesses(self.X)
        Ty, Tb = self.hdr([(self.x, 0)], "1"), self.hdr([(self.s, 0), (self.x, 0)], "2")
        seal_y = model.seal_from_votes([w.spend(self.req(Ty, self.x, self.px)) for w in k])
        for w in k[:3]:
            w.spend(self.req(Tb, self.s, self.ps))
        dp = {"kind": "seal", "sigil": self.x, "gen": 0, "parcel": self.tgt(self.px), "seal": seal_y}
        for w in k[:3]:
            w.release(self.s, dp)                    # Tb is dead: x went to Ty
        honest = [e for e in k[0].records[self.s].log]   # bind Tb, release Tb
        # Junk a Byzantine predecessor could send, every item individually plausible:
        Tz = self.hdr([(self.s, 0), (self.x, 0)], "9")    # never bound, but Ty's seal "proves" it dead
        other = KeyPair.generate()
        stranger_vote = {"constellation": self.X, "version": 0, "witness": other.pk, "sigil": self.s,
                         "gen": 0, "tid": "7" * 64, "time": 1}
        stranger_vote["sig"] = other.sign("vote", model.vote_payload(stranger_vote))
        junk = {self.s: [
            {"kind": "release", "gen": 0, "tid": model.transition_id(Tz), "header": Tz, "proof": dp},
            {"kind": "vote", "vote": stranger_vote},
            {"kind": "bind", "gen": 0, "auth": None},
            {"kind": "release", "gen": 0, "tid": "8" * 64, "header": Tz, "proof": {}},
            {"kind": "mystery"},
        ]}
        a, _ = self.rotate_with(junk)
        log = a.records[self.s].log
        kinds = sorted(e["kind"] for e in log)
        self.assertEqual(kinds, ["bind", "release"], log)
        self.assertEqual({model.transition_id(e["auth"]["header"]) for e in log if e["kind"] == "bind"},
                         {model.transition_id(Tb)})
        self.assertEqual({e["tid"] for e in log if e["kind"] == "release"}, {model.transition_id(Tb)})
        self.assertEqual(len(log), len(honest))
        # The decision is unchanged: Tb is dead, so s is free at generation 1.
        self.assertEqual((a.records[self.s].gen, a.records[self.s].tid), (1, None))

    def test_junk_does_not_survive_later_rotations(self):
        k = self.net.witnesses(self.X)
        T1 = self.hdr([(self.s, 0)], "1")
        for w in k:
            w.spend(self.req(T1, self.s, self.ps))
        junk = {self.s: [{"kind": "bind", "gen": i, "auth": {"header": T1}} for i in range(50)]}
        a, _ = self.rotate_with(junk)
        self.assertEqual(len(a.records[self.s].log), 1)   # the one real binding
        self.assertEqual(a.records[self.s].tid, model.transition_id(T1))
        # What a1 would hand to the next version carries no junk either.
        nxt = charter_body("orion", 2, [KeyPair.generate().pk],
                           charter_hash(self.net.registry.latest(self.X)))
        _sig, snap = a.freeze(nxt)
        self.assertEqual([e["kind"] for e in snap[self.s]], ["bind"])


if __name__ == "__main__":
    unittest.main()
