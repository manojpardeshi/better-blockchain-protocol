"""Malicious handovers over the wire: ``/v0/adopt`` and ``/v0/standby`` fed by a Byzantine predecessor.

A rotation's or succession's new members ADOPT (SPEC §5.4), and a new committee enters STANDBY
(§5.5), from snapshots the operator collected from the old version's members or standby members,
any *f* of which may be Byzantine. Each case here crafts such snapshots (forged, padded,
contradicting, replayed from another constellation or version, oversized, holding values only one
implementation can represent) and sends them to a *twin pair* (a Rust and a Python process with the
same key, ``compat_harness.Daemon``), then compares, between the twins and against what the
evidence must yield:

* the reply (an operator call refused by one twin and accepted by the other is a wire divergence,
  and a refusal caused by junk one Byzantine predecessor added is a liveness failure: the new
  version can never be completed);
* the inherited state (STATUS of every sigil in the evidence, or the standby member's bindings);
* what the new member carries forward: the snapshot it hands its own successor (FREEZE, or
  SUCCEED for a standby member), which must hold no padding.

Run with the Rust binary built (``cargo build --release --locked --manifest-path rust/Cargo.toml``).
"""

import json
import os
import time
import unittest

from sigil import locks, model
from sigil.charter import charter_body, charter_hash, sign_charter, successor_clause
from sigil.crypto import KeyPair
from sigil.witnessd import load_key

from tests.integration.compat_harness import (Daemon, http, make_tmpdir, new_constellation, requires_rust,
                                              wait_http, witnessd, write_token)

OWNER = KeyPair.from_seed(b"\x11" * 32)
MALLORY = KeyPair.from_seed(b"\x12" * 32)


def strip_votes(x):
    """Votes compared without ``time``/``sig`` (two processes may straddle a second)."""
    if isinstance(x, dict):
        if {"witness", "sig", "time", "tid"} <= set(x):
            return {k: v for k, v in x.items() if k not in ("time", "sig")}
        return {k: strip_votes(v) for k, v in x.items()}
    if isinstance(x, list):
        return [strip_votes(v) for v in x]
    return x


@requires_rust
class HandoverAdversary(unittest.TestCase):
    """A predecessor (or standby member) of the new version is Byzantine; the new member is honest."""

    @classmethod
    def setUpClass(cls):
        d = cls.dir = make_tmpdir(cls, "handover")
        cls.token, cls.token_file = write_token(d)
        cls.tok = {"Authorization": f"Bearer {cls.token}"}
        c = new_constellation(d, "orion", 4)
        cls.cid = c["cid"]
        cls.old = [load_key(k) for k in c["keys"]]
        with open(c["registry"]) as f:
            cls.chain0 = json.load(f)[cls.cid]
        v0 = cls.chain0[0]["body"]
        # Version 1: three old keys and one new key (the twins' key); a successor committee of 4.
        cls.newkey_file = os.path.join(d, "keys", "newmember.json")
        witnessd("keygen", "--out", cls.newkey_file)
        cls.me = load_key(cls.newkey_file)
        cls.kfiles = [os.path.join(d, "keys", f"k{i}.json") for i in range(4)]
        for k in cls.kfiles:
            witnessd("keygen", "--out", k)
        cls.ckeys = [load_key(k) for k in cls.kfiles]
        v1 = charter_body(v0["name"], 1, [k.pk for k in cls.old[:3]] + [cls.me.pk], charter_hash(v0),
                          successor_clause([k.pk for k in cls.ckeys], 60))
        cls.chain1 = cls.chain0 + [{"body": v1, "sigs": {k.pk: sign_charter(k, v1) for k in cls.old[:3]}}]
        # Version 2 (what the twins freeze or succeed for, to read what they carry forward).
        cls.v2 = charter_body(v0["name"], 2, [k.pk for k in cls.old[:3]] + [cls.me.pk], charter_hash(v1))
        cls.v2sigs = {k.pk: sign_charter(k, cls.v2) for k in cls.old[:3]}
        cls.logs = os.path.join(d, "logs")
        os.makedirs(cls.logs)
        cls.n = 0

    # ------------------------------------------------------------ evidence builders

    def parcel(self, salt: str, key=OWNER, cid=None):
        p = model.parcel(cid or self.cid, "x", 1, locks.sig(key.pk), salt)
        return p, model.sigil_of(p)

    @staticmethod
    def hdr(inputs, tag: str) -> dict:
        return {"inputs": [list(i) for i in inputs], "body": (tag * 64)[:64]}

    def auth(self, h, sigil, p, exp=None, key=OWNER):
        exp = int(time.time()) + 600 if exp is None else exp
        u = locks.empty_unlock(exp)
        u["sigs"][key.pk] = locks.sign_unlock(key, sigil, model.transition_id(h), exp)
        return {"home": p["home"], "lock": p["lock"], "salt": p["salt"], "unlock": u, "header": h}

    def bind(self, h, sigil, p, gen, **kw):
        return {"kind": "bind", "gen": gen, "auth": self.auth(h, sigil, p, **kw)}

    def vote(self, kp, sigil, gen, tid, version=0, cid=None):
        v = {"constellation": cid or self.cid, "version": version, "witness": kp.pk, "sigil": sigil, "gen": gen,
             "tid": tid, "time": 1_700_000_000}
        v["sig"] = kp.sign("vote", model.vote_payload(v))
        return v

    def seal(self, sigil, gen, tid, keys=None):
        return model.seal_from_votes([self.vote(k, sigil, gen, tid) for k in (keys or self.old[:3])])

    def death_by_seal(self, sigil, gen, p, other_tid):
        return {"kind": "seal", "sigil": sigil, "gen": gen,
                "parcel": {"home": p["home"], "lock": p["lock"], "salt": p["salt"]},
                "seal": self.seal(sigil, gen, other_tid)}

    # ------------------------------------------------------------ twins

    def twins(self, role: str = "witness"):
        """A fresh Rust/Python pair holding the new member's key (``--adopt``), or a committee
        member's (``standby --wait``), both knowing version 1."""
        self.__class__.n += 1
        name = f"{role}{self.n}"
        out = []
        for kind, ext in (("rust", "redb"), ("python", "db")):
            key = self.newkey_file if role == "witness" else self.kfiles[0]
            extra = ["--adopt"] if role == "witness" else ["--wait"]
            dmn = Daemon(kind, key, self._reg(),
                         self.cid, os.path.join(self.dir, f"{name}-{kind}.{ext}"),
                         os.path.join(self.logs, f"{name}-{kind}.log"), role=role,
                         args=["--admin-token", self.token_file, *extra])
            dmn.start(wait=False)
            self.addCleanup(dmn.stop)
            out.append(dmn)
        for dmn in out:
            wait_http(dmn.url, proc=dmn.proc, log=dmn.log)
            code, body, _ = http(dmn.url, "/v0/gossip", {"charters": {self.cid: self.chain1}})
            self.assertEqual(code, 200, body)
        return out

    def _reg(self) -> str:
        path = os.path.join(self.dir, "registry.json")
        return path

    def handover(self, snapshots: list, role: str = "witness", raw: bytes | None = None):
        """Send the handover to fresh twins; returns ``(twins, [(code, body)] per twin)``."""
        pair = self.twins(role)
        path = "/v0/adopt" if role == "witness" else "/v0/standby"
        body = {"constellation": self.cid, "version": 1, "snapshots": snapshots}
        replies = []
        for dmn in pair:
            code, rep, _ = http(dmn.url, path, None if raw is not None else body, raw=raw, headers=self.tok,
                                timeout=120)
            replies.append((code, rep))
        return pair, replies

    def state(self, dmn, role: str, sigils) -> dict:
        out = {}
        for s in sigils:
            code, rep, _ = http(dmn.url, "/v0/status", {"sigil": s})
            out[s] = (code, strip_votes(rep))
        return out

    def carried(self, dmn, role: str) -> dict:
        """The snapshot the twin hands its own successor (FREEZE / cooperative SUCCEED for v2)."""
        if role == "witness":
            code, rep, _ = http(dmn.url, "/v0/freeze", {"charter": self.v2}, headers=self.tok, timeout=120)
        else:
            code, rep, _ = http(dmn.url, "/v0/succeed", {"charter": self.v2, "sigs": self.v2sigs},
                                headers=self.tok, timeout=120)
        self.assertEqual(code, 200, rep)
        return strip_votes(rep["ok"]["snapshot"])

    def compare(self, snapshots, sigils, role: str = "witness", raw: bytes | None = None, expect_code: int = 200):
        """Both twins accept (``expect_code``), inherit the same state, and carry forward the
        same snapshot; returns ``(states, carried)`` of the Python twin for further checks."""
        pair, replies = self.handover(snapshots, role, raw)
        (rc, rb), (pc, pb) = replies
        self.assertEqual((rc, pc), (expect_code, expect_code),
                         f"handover answered differently: rust {rc} {str(rb)[:300]}, python {pc} {str(pb)[:300]}")
        if expect_code != 200:
            return None, None
        rs, ps = (self.state(dmn, role, sigils) for dmn in pair)
        self.assertEqual(rs, ps, "inherited state differs between Rust and Python")
        rcar, pcar = (self.carried(dmn, role) for dmn in pair)
        self.assertEqual(rcar, pcar, "Rust and Python carry different evidence forward")
        return ps, pcar

    # ------------------------------------------------------------ fixtures of evidence

    def honest_evidence(self):
        """sigil a bound to Ta at 0 (sealed); b bound to Tb at 0 then released (death by seal of a
        sibling), bound again at 1 to Tb2; c: nothing. Returns ``(snapshot, info)``."""
        pa, a = self.parcel("a1" * 16)
        pb, b = self.parcel("b1" * 16)
        pq, q = self.parcel("c1" * 16)
        Ta = self.hdr([(a, 0)], "a")
        Tb = self.hdr([(b, 0), (q, 0)], "b")       # a swap whose other input q was spent elsewhere
        Tq = self.hdr([(q, 0)], "c")
        Tb2 = self.hdr([(b, 1)], "d")
        ta, tb, tq, tb2 = (model.transition_id(h) for h in (Ta, Tb, Tq, Tb2))
        rel = {"kind": "release", "gen": 0, "tid": tb, "header": Tb, "proof": self.death_by_seal(q, 0, pq, tq)}
        snap = {
            a: [self.bind(Ta, a, pa, 0), {"kind": "seal", "seal": self.seal(a, 0, ta)}],
            b: [self.bind(Tb, b, pb, 0), rel, self.bind(Tb2, b, pb, 1)],
        }
        return snap, {"a": (a, ta), "b": (b, tb2), "tb": tb, "pa": pa, "pb": pb}

    # ------------------------------------------------------------ cases

    def test_honest_evidence_identical(self):
        """Control: a well-formed handover gives the same records on both twins."""
        snap, info = self.honest_evidence()
        a, b = info["a"][0], info["b"][0]
        for role in ("witness", "standby"):
            with self.subTest(role=role):
                st, car = self.compare([snap, snap], [a, b], role)
                if role == "witness":
                    self.assertEqual((st[a][1]["ok"]["gen"], st[a][1]["ok"]["tid"]), (0, info["a"][1]))
                    self.assertEqual((st[b][1]["ok"]["gen"], st[b][1]["ok"]["tid"]), (1, info["b"][1]))
                else:
                    self.assertIn([0, info["a"][1]], st[a][1]["ok"]["bindings"])

    def test_forged_and_replayed_entries_are_skipped(self):
        """Forged signatures, a bind for another constellation (replayed from elsewhere), a seal of
        too few members, a vote by another key, a release whose proof does not verify: none of
        them is inherited, none is carried forward, and both twins agree."""
        snap, info = self.honest_evidence()
        a, ta = info["a"]
        pa = info["pa"]
        forged = self.bind(self.hdr([(a, 0)], "f"), a, pa, 0)
        forged["auth"]["unlock"]["sigs"][OWNER.pk] = "00" * 64
        other = "ee" * 32
        po, so = self.parcel("e1" * 16, cid=other)
        replay = self.bind(self.hdr([(so, 0)], "e"), so, po, 0)            # its home is another cid
        thin = {"kind": "seal", "seal": self.seal(a, 0, model.transition_id(self.hdr([(a, 0)], "9")), self.old[:2])}
        alien = {"kind": "vote", "vote": self.vote(MALLORY, a, 0, "99" * 32)}
        badrel = {"kind": "release", "gen": 0, "tid": ta, "header": self.hdr([(a, 0)], "a"),
                  "proof": {"kind": "seal", "sigil": a, "gen": 0, "parcel": {}, "seal": {}}}
        evil = {a: [forged, thin, alien, badrel], so: [replay]}
        for role in ("witness", "standby"):
            with self.subTest(role=role):
                st, car = self.compare([evil, snap], [a, so], role)   # (so: a parcel of another home, inert)
                self.assertEqual(car.get(a), snap[a], "only the honest entries are carried forward")
                if role == "witness":
                    self.assertEqual(st[a][1]["ok"]["tid"], ta)

    def test_contradicting_snapshots_make_the_record_contested(self):
        """The owner equivocated (two tids bound at generation 0, no seal in the evidence): one
        Byzantine predecessor hands over the second binding. Neither is inherited as bound."""
        pa, a = self.parcel("a2" * 16)
        T1, T2 = self.hdr([(a, 0)], "1"), self.hdr([(a, 0)], "2")
        honest = {a: [self.bind(T1, a, pa, 0)]}
        evil = {a: [self.bind(T2, a, pa, 0)]}
        st, car = self.compare([honest, evil, honest], [a])
        self.assertEqual(st[a][1]["ok"]["tid"], "!contested")
        st, car = self.compare([honest, evil], [a], "standby")
        self.assertEqual(len(st[a][1]["ok"]["bindings"]), 2)

    def test_padding_is_not_carried_forward(self):
        """A Byzantine predecessor pads its snapshot: junk entries of every shape under real sigils,
        and thousands of made-up sigils holding only junk. The new member keeps only verified
        evidence, and hands none of the padding to its own successor (SPEC §5.4 "The new
        record's log"): neither entries nor empty records under made-up sigils."""
        snap, info = self.honest_evidence()
        a, b = info["a"][0], info["b"][0]
        junk = [7, None, "x", [1], {}, {"kind": "bind"}, {"kind": "bind", "auth": 5}, {"kind": "seal", "seal": []},
                {"kind": "release", "tid": "00"}, {"kind": "vote", "vote": {"gen": 0}}, {"kind": "zzz", "pad": "p" * 100}]
        pad = {a: junk * 50, b: list(junk)}
        for k in range(3000):
            pad[f"{k:064x}"] = [{"kind": "bind", "n": k}]
        for k in range(1000):
            pad[f"f{k:063x}"] = []
        for role in ("witness", "standby"):
            with self.subTest(role=role):
                st, car = self.compare([snap, pad], [a, b, f"{5:064x}"], role)
                self.assertEqual(car.get(a), snap[a])
                made_up = [s for s in car if s not in (a, b)]
                self.assertEqual(made_up, [], f"{len(made_up)} made-up sigils carried forward")

    def test_oversized_handover_is_accepted(self):
        """A snapshot of 24 MiB of junk next to the honest one: the handover (whose body may be up to
        256 MiB) still completes on both twins, with the honest bindings."""
        snap, info = self.honest_evidence()
        a = info["a"][0]
        big = {a: [{"kind": "zzz", "pad": "z" * (1 << 20)} for _ in range(24)]}
        st, car = self.compare([big, snap], [a])
        self.assertEqual(st[a][1]["ok"]["tid"], info["a"][1])

    def test_unportable_values_in_a_byzantine_snapshot(self):
        """One Byzantine predecessor puts values in its FREEZE snapshot that only one
        implementation can represent: NaN, Infinity, a float out of range, integers beyond 128
        bits, a lone UTF-16 surrogate, deep nesting. Relayed as they are, they made every Rust
        adopter (and standby member) refuse the whole handover while the Python one accepted it,
        so one Byzantine predecessor could keep a rotation from ever completing (the honest
        snapshots are in the same request).

        Now both daemons refuse a body that is not portable JSON (WIRE.md), identically, and the
        operator's client (``RemoteWitness.freeze``, ``RemoteStandby.succeed``) drops such entries
        from the snapshots it collects (``portable_snapshot``): they can never verify, since no
        witness of either kind accepts a request holding one. The cleaned handover completes on
        both twins with the honest evidence."""
        from sigil.server import portable_snapshot
        snap, info = self.honest_evidence()
        a = info["a"][0]
        pieces = {
            "nan": b'{"kind":"zzz","x":NaN}',
            "infinity": b'{"kind":"zzz","x":-Infinity}',
            "float out of range": b'{"kind":"zzz","x":1e999}',
            "int beyond 128 bits": b'{"kind":"zzz","x":' + str(1 << 130).encode() + b"}",
            "lone surrogate": b'{"kind":"zzz","x":"\\ud800"}',
            "deep nesting": b'{"kind":"zzz","x":' + b"[" * 400 + b"]" * 400 + b"}",
        }
        honest = json.dumps(snap).encode()
        for name, piece in pieces.items():
            evil_raw = b'{"' + a.encode() + b'":[' + piece + b"," + json.dumps(snap[a][0]).encode() + b"]}"
            for role in ("witness", "standby"):
                with self.subTest(value=name, role=role):
                    raw = (b'{"constellation":"' + self.cid.encode() + b'","version":1,"snapshots":['
                           + honest + b"," + evil_raw + b"]}")
                    self.compare(None, [a], role, raw=raw, expect_code=400)   # identical refusal
                    evil = json.loads(evil_raw)            # what the operator's client parsed
                    cleaned = portable_snapshot(evil)
                    self.assertEqual(cleaned, {a: [snap[a][0]]})
                    st, car = self.compare([snap, cleaned], [a], role)
                    self.assertEqual(car.get(a), snap[a])

    def test_generation_beyond_the_shared_range(self):
        """An owner (colluding with a Byzantine predecessor) signs a binding at generation 2**62:
        Python's ``authorises`` accepts any non-negative integer, Rust's stops below 2**62. The two
        implementations must inherit the same record from the same evidence."""
        pa, a = self.parcel("a3" * 16)
        T0, Tbig = self.hdr([(a, 0)], "0"), self.hdr([(a, 1 << 62)], "9")
        snap = {a: [self.bind(T0, a, pa, 0), self.bind(Tbig, a, pa, 1 << 62)]}
        for role in ("witness", "standby"):
            with self.subTest(role=role):
                self.compare([snap], [a], role)

    def test_release_citing_an_unknown_home_is_kept_by_standby(self):
        """REVIEW FINDING (Medium). A swap of a (homed here) and q (homed at lyra) died: q was
        spent elsewhere and sealed by lyra. The release's death proof cites lyra, whose chain the
        standby member does not know, so it cannot verify it, and STANDBY used to drop it for
        good; after a takeover the successor would find a bound to the dead swap. Now a standby
        member keeps such a release for a binding it holds (once per tid, within the proof cap),
        for an adopter that knows lyra to verify."""
        d = make_tmpdir(self, "lyra")
        ly = new_constellation(d, "lyra", 4)
        lkeys = [load_key(k) for k in ly["keys"]]
        pa, a = self.parcel("a5" * 16)
        pq, q = self.parcel("c5" * 16, cid=ly["cid"])
        Tsw, Tq = self.hdr([(a, 0), (q, 0)], "5"), self.hdr([(q, 0)], "6")
        tsw, tq = model.transition_id(Tsw), model.transition_id(Tq)
        seal = model.seal_from_votes([self.vote(k, q, 0, tq, cid=ly["cid"]) for k in lkeys[:3]])
        proof = {"kind": "seal", "sigil": q, "gen": 0, "parcel": {k: pq[k] for k in ("home", "lock", "salt")},
                 "seal": seal}
        rel = {"kind": "release", "gen": 0, "tid": tsw, "header": Tsw, "proof": proof}
        # A Byzantine predecessor's junk release for the same tid, ordered first: it cites a made-up
        # home (so no member can verify it) with padding, but fails the charter-free checks.
        junk = dict(rel, proof=dict(proof, parcel=dict(proof["parcel"], home="ee" * 32), pad="p" * 100_000))
        variant = dict(rel, proof=dict(proof, pad="x"))
        snap = {a: [self.bind(Tsw, a, pa, 0), junk, rel, variant]}
        st, car = self.compare([snap], [a], "standby")
        self.assertEqual(car.get(a), [snap[a][0], rel, variant], "the plausible releases are carried, not the junk")
        # A member that learns lyra and is then sent the release verifies it; the unverifiable ones
        # it kept give way to it.
        # A plausible fake (votes by keys that are not lyra's members) is all it holds at first.
        fakes = [KeyPair.from_seed(bytes([40 + i]) * 32) for i in range(3)]
        fake = dict(rel, proof=dict(proof, seal=model.seal_from_votes(
            [self.vote(k, q, 0, tq, cid=ly["cid"]) for k in fakes])))
        pair, replies = self.handover([{a: [snap[a][0], fake]}], "standby")
        chain = json.load(open(ly["registry"]))[ly["cid"]]
        for dmn in pair:
            http(dmn.url, "/v0/gossip", {"charters": {ly["cid"]: chain}})
            code, rep, _ = http(dmn.url, "/v0/note_release", {"sigil": a, "entry": rel})
            self.assertEqual((code, rep.get("ok")), (200, True), dmn.kind)
            code, rep, _ = http(dmn.url, "/v0/note_release", {"sigil": a, "entry": rel})
            self.assertEqual((code, rep.get("ok")), (200, False), dmn.kind)
        rcar, pcar = (self.carried(dmn, "standby") for dmn in pair)
        self.assertEqual(rcar, pcar)
        self.assertEqual(pcar[a], [snap[a][0], rel])
        # Evidence from a version of lyra the member does not know yet is kept too (structurally checked).
        b1 = charter_body("lyra", 1, [k.pk for k in lkeys], charter_hash(chain[0]["body"]))
        votes1 = []
        for k in lkeys[:3]:
            v = {"constellation": ly["cid"], "version": 1, "witness": k.pk, "sigil": q, "gen": 0, "tid": tq,
                 "time": 1_700_000_000}
            v["sig"] = k.sign("vote", model.vote_payload(v))
            votes1.append(v)
        rel1 = dict(rel, proof=dict(proof, seal=model.seal_from_votes(votes1)))
        snap1 = {a: [self.bind(Tsw, a, pa, 0), rel1]}
        for dmn in self.twins("standby"):   # it knows lyra version 0 only
            http(dmn.url, "/v0/gossip", {"charters": {ly["cid"]: chain}})
            code, rep, _ = http(dmn.url, "/v0/standby", {"constellation": self.cid, "version": 1, "snapshots": [snap1]},
                                headers=self.tok)
            self.assertEqual(code, 200, rep)
            self.assertEqual(self.carried(dmn, "standby").get(a), snap1[a], dmn.kind)
        # A witness that knows lyra verifies it: the binding is dead, a is free at generation 1.
        pair = self.twins("witness")
        for dmn in pair:
            http(dmn.url, "/v0/gossip", {"charters": {ly["cid"]: json.load(open(ly["registry"]))[ly["cid"]]}})
            code, _r, _ = http(dmn.url, "/v0/adopt", {"constellation": self.cid, "version": 1, "snapshots": [car]},
                               headers=self.tok)
            self.assertEqual(code, 200)
            ok = http(dmn.url, "/v0/status", {"sigil": a})[1]["ok"]
            self.assertEqual((ok["gen"], ok["tid"]), (1, None))

    def test_standby_drops_votes_on_made_up_sigils(self):
        """REVIEW FINDING (Low). A Byzantine former member pads the mirror with valid votes of its
        own on made-up sigils. A vote is now kept only for a sigil with a kept binding, or if its
        signer is a member of the version handed over (a re-used key's own votes must travel)."""
        snap, info = self.honest_evidence()
        a = info["a"][0]
        former, member = self.old[3], self.old[0]           # old[3] is not in version 1
        pad = {f"{k:064x}": [{"kind": "vote", "vote": self.vote(former, f"{k:064x}", 0, "ab" * 32)}]
               for k in range(50)}
        keep = {"cd" * 32: [{"kind": "vote", "vote": self.vote(member, "cd" * 32, 0, "ab" * 32)}]}
        st, car = self.compare([snap, pad, keep], [a], "standby")
        self.assertEqual(sorted(car), sorted([a, info["b"][0], "cd" * 32]))

    def test_expiry_beyond_128_bits(self):
        """A binding whose authorisation expires at 2**130 (the owner signed it; an honest wallet
        never does). Python used to bind such a SPEND while Rust could not parse it, so a quorum
        of Python witnesses could seal a transition no Rust successor could ever inherit (it
        refused the handover). Now both refuse the SPEND and the handover alike."""
        pa, a = self.parcel("a4" * 16)
        T = self.hdr([(a, 0)], "4")
        snap = {a: [self.bind(T, a, pa, 0, exp=1 << 130)]}
        for role in ("witness", "standby"):
            with self.subTest(role=role):
                self.compare([snap], [a], role, expect_code=400)
        # The SPEND itself, at twins that joined version 1 (an empty handover).
        pair, replies = self.handover([])
        self.assertEqual([c for c, _ in replies], [200, 200])
        req = dict(self.auth(T, a, pa, exp=1 << 130), sigil=a)
        codes = [http(dmn.url, "/v0/spend", {"request": req})[0] for dmn in pair]
        self.assertEqual(codes, [400, 400])

if __name__ == "__main__":
    unittest.main()
