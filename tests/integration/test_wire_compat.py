"""Wire compatibility: every endpoint of docs/WIRE.md answers identically from Rust and Python.

Each comparison runs a *twin pair*: a Rust and a Python process holding the **same key**,
registry and constellation, on separate stores, so their answers must be identical JSON
(Ed25519 is deterministic; only a vote's ``time``, and so its ``sig``, may differ when the two
answers straddle a second, so votes are compared without them after their signatures are
checked). Every request is sent to both twins in the same order, and the HTTP status, the
error kind, the message and the result must match.

The requests are generated from WIRE.md: the endpoint tables are parsed, and every endpoint
listed there gets the generic cases (not JSON, not an object, missing fields, each field of
the wrong type, a body over the cap, admin calls without / with a wrong / with the token)
plus its specific cases (valid calls, conflicts, the size caps of SPEND, RELEASE and MIRROR,
the generation limit, the gossip and charter caps, rate limiting). A WIRE.md endpoint with no
generated case fails the test, so the document and this suite cannot drift apart.

Known, documented differences (docs/BENCHMARKS.md "Compatibility notes") are listed in
``KNOWN`` with the reason; anything else that differs is a failure.
"""

import json
import os
import re
import shutil
import time
import unittest

from sigil import locks, model
from sigil.charter import MAX_WITNESSES, charter_body, charter_hash, constellation_id, sign_charter
from sigil.crypto import KeyPair, verify
from sigil.witnessd import load_key, load_mint

from tests.integration.compat_harness import (ROOT, Daemon, http, make_tmpdir, new_constellation, requires_rust,
                                       wait_http, witnessd, write_token)

WIRE = os.path.join(ROOT, "docs", "WIRE.md")
MIB = 1 << 20
TYPE_FUZZ = [None, 5, "x", [], {}, True, -1]


def wire_endpoints() -> dict:
    """``{(role, method, path): admin}`` for every endpoint row of the WIRE.md tables."""
    out, role = {}, "witness"
    for line in open(WIRE, encoding="utf-8"):
        if line.startswith("## "):
            role = "standby" if line.strip() == "## Succession" else "witness"
        if not line.startswith("| GET") and not line.startswith("| POST"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        method = cells[0]
        # e.g. "`/v0/charters`, `/v0/proofs`; POST `/v0/gossip`": a later verb applies onwards
        for part in re.split(r";\s*", cells[1]):
            m = re.match(r"(GET|POST)\s+(.*)", part)
            if m:
                method, part = m.group(1), m.group(2)
            for path in re.findall(r"`(/v0/[a-z_]+)`", part):
                out[(role, method, path)] = "(admin)" in part
    return out


def load_json(path: str):
    with open(path) as f:
        return json.load(f)


def is_vote(x) -> bool:
    return isinstance(x, dict) and {"witness", "sig", "time", "tid", "sigil"} <= set(x)


def normalise(x, bad_sigs: list):
    """Strip ``time`` and ``sig`` from votes (after checking the signature), recursively."""
    if isinstance(x, dict):
        if is_vote(x):
            try:
                ok = verify(x["witness"], "vote", model.vote_payload(x), x["sig"])
            except Exception:  # noqa: BLE001 - a malformed vote is a bad signature
                ok = False
            if not ok:
                bad_sigs.append(x)
            x = {k: v for k, v in x.items() if k not in ("time", "sig")}
        return {k: normalise(v, bad_sigs) for k, v in x.items()}
    if isinstance(x, list):
        return [normalise(v, bad_sigs) for v in x]
    return x


# Differences the project documents as deliberate (docs/BENCHMARKS.md "Compatibility notes":
# "the Rust witness may refuse what the reference accepts, never the reverse"), and minor ones
# pinned by an expectedFailure test in test_bugs_found.py. Keyed by case name; the value says
# why. A listed case must still answer an error on the Rust side.
KNOWN: dict = {
    "sell_stamp 0x prefix": "deliberate: hex in stamps must be plain [0-9a-fA-F]+ (BENCHMARKS.md)",
    "witness GET unknown": "bug: Rust answers 405 with no JSON body (test_bugs_found.RustGetUnknownPath)",
    "standby GET unknown": "bug: Rust answers 405 with no JSON body (test_bugs_found.RustGetUnknownPath)",
    "witness GET a POST path": "bug: Rust answers 405 with no JSON body (test_bugs_found.RustGetUnknownPath)",
    "standby GET a POST path": "bug: Rust answers 405 with no JSON body (test_bugs_found.RustGetUnknownPath)",
    "witness POST v1": "minor: a path outside /v0/ is 404 in Rust, 400 in Python; both bad_request",
    "standby POST v1": "minor: a path outside /v0/ is 404 in Rust, 400 in Python; both bad_request",
}


def comparable(code: int, body, retry: bool):
    """What must match: status, kind, result and vote always; the message unless the status is
    400 (``bad_request`` messages are implementation text: Python exception strings, parser
    errors; WIRE.md defines only the kind)."""
    if isinstance(body, dict) and "error" in body and code == 400:
        body = {k: v for k, v in body.items() if k != "message"}
    return code, body, retry


class Recorder:
    """Sends each case to both twins and collects the differences."""

    def __init__(self):
        self.diffs: list = []
        self.covered: set = set()
        self.cases = 0
        self.soft: list = []
        self.messages: list = []   # bad_request message differences (reported, not failures)

    def send(self, name: str, twins: tuple, role: str, path: str, body=None, *, raw: bytes | None = None,
             method: str | None = None, headers: dict | None = None, expect: int | None = None):
        rust, py = twins
        method = method or ("GET" if body is None and raw is None else "POST")
        self.covered.add((role, method, path))
        self.cases += 1
        a = http(rust.url, path, body, raw=raw, method=method, headers=headers)
        b = http(py.url, path, body, raw=raw, method=method, headers=headers)
        bad: list = []
        ra = (a[0], normalise(a[1], bad), "retry-after" in a[2])
        rb = (b[0], normalise(b[1], bad), "retry-after" in b[2])
        if bad:
            self.diffs.append((name, "invalid vote signature", bad))
        if comparable(*ra) != comparable(*rb):
            if name in KNOWN and a[0] >= 400:
                self.soft.append((name, KNOWN[name], ra, rb))
            else:
                self.diffs.append((name, {"rust": ra, "python": rb}))
        elif ra != rb:
            self.messages.append((name, ra[1].get("message"), rb[1].get("message")))
        if expect is not None and b[0] != expect:
            self.diffs.append((name, f"python answered {b[0]}, expected {expect}", rb))
        return b[1]

    def generic(self, twins, role: str, path: str, fields: list, token: str | None = None, admin: bool = False):
        """The generic cases of one POST endpoint."""
        auth = {"Authorization": f"Bearer {token}"} if admin and token else None
        n = f"{role}{path}"
        if admin:
            self.send(f"{n} no token", twins, role, path, {})
            self.send(f"{n} wrong token", twins, role, path, {}, headers={"Authorization": "Bearer nope"})
            self.send(f"{n} not bearer", twins, role, path, {}, headers={"Authorization": token or "x"})
        self.send(f"{n} not json", twins, role, path, raw=b"not json", headers=auth)
        self.send(f"{n} array body", twins, role, path, raw=b"[]", headers=auth)
        self.send(f"{n} empty body", twins, role, path, raw=b"", headers=auth)
        self.send(f"{n} missing fields", twins, role, path, {}, headers=auth)
        if not admin:
            pad = b'{"pad": "' + b"x" * MIB + b'"}'
            self.send(f"{n} over 1 MiB", twins, role, path, raw=pad, headers=auth, expect=400)
        for f in fields:
            for v in TYPE_FUZZ:
                body = {g: (v if g == f else None) for g in fields}
                body[f] = v
                self.send(f"{n} {f}={json.dumps(v)}", twins, role, path, body, headers=auth)


@requires_rust
class WireCompatTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = cls.dir = make_tmpdir(cls, "wire")
        cls.token, cls.token_file = write_token(d)
        c = cls.c = new_constellation(d, "twin", 4)
        cls.cid, cls.reg = c["cid"], c["registry"]
        cls.wkeys = [load_key(k) for k in c["keys"]]
        cls.k4 = os.path.join(d, "keys", "new-member.json")   # a member of version 1 only
        witnessd("keygen", "--out", cls.k4)
        logs = os.path.join(d, "logs")
        os.makedirs(logs)

        def twin(name, key, extra=(), role="witness", cid=None, registry=None):
            ds = []
            for kind, ext in (("rust", "redb"), ("python", "db")):
                ds.append(Daemon(kind, key, registry or cls.reg, cid or cls.cid, os.path.join(d, f"{name}-{kind}.{ext}"),
                                 os.path.join(logs, f"{name}-{kind}.log"), role=role,
                                 args=["--admin-token", cls.token_file, *extra]))
            return tuple(ds)

        cls.twin = staticmethod(twin)
        # The stamped twins share one stamp key, so their blind signatures are identical.
        mint = load_mint(os.path.join(d, "stamped-python.db.stamps.json"))
        shutil.copy(os.path.join(d, "stamped-python.db.stamps.json"), os.path.join(d, "stamped-rust.redb.stamps.json"))
        cls.mint_pub = mint.public
        cls.plain = twin("plain", c["keys"][0])
        cls.stamped = twin("stamped", c["keys"][1], ["--stamps"])
        cls.limited = twin("limited", c["keys"][2], ["--rate-limit", "1", "--rate-burst", "3"])
        # A constellation with a successor committee, for the standby calls (no probing).
        s = cls.s = new_constellation(d, "heir", 4, committee=4, dead_man=1)
        cls.skeys = [load_key(k) for k in s["keys"]]
        cls.ckeys = [load_key(k) for k in s["committee"]]
        cls.standby = twin("standby", s["committee"][0], role="standby", cid=s["cid"], registry=s["registry"])
        cls.heirw = twin("heirw", s["keys"][0], cid=s["cid"], registry=s["registry"])
        for t in (cls.plain, cls.stamped, cls.limited, cls.standby, cls.heirw):
            for dmn in t:
                dmn.start(wait=False)
                cls.addClassCleanup(dmn.stop)
        for t in (cls.plain, cls.stamped, cls.limited, cls.standby, cls.heirw):
            for dmn in t:
                wait_http(dmn.url, proc=dmn.proc, log=dmn.log)
        cls.owner = KeyPair.from_seed(b"\x07" * 32)
        cls.rec = Recorder()

    # ------------------------------------------------------------ builders

    def parcel(self, salt: str, cid=None, lock=None):
        p = model.parcel(cid or self.cid, "x", 1, lock or locks.sig(self.owner.pk), salt)
        return p, model.sigil_of(p)

    @staticmethod
    def hdr(inputs, tag: str) -> dict:
        return {"inputs": [list(i) for i in inputs], "body": tag * 64}

    def req(self, h, sigil, p, exp=None, signer=None):
        exp = int(time.time()) + 600 if exp is None else exp
        u = locks.empty_unlock(exp)
        u["sigs"][(signer or self.owner).pk] = locks.sign_unlock(signer or self.owner, sigil, model.transition_id(h), exp)
        return {"sigil": sigil, "header": h, "home": p["home"], "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def vote(self, kp, cid, sigil, gen, tid, version=0):
        v = {"constellation": cid, "version": version, "witness": kp.pk, "sigil": sigil, "gen": gen, "tid": tid,
             "time": 1_700_000_000}
        v["sig"] = kp.sign("vote", model.vote_payload(v))
        return v

    def seal(self, keys, cid, sigil, gen, tid):
        return model.seal_from_votes([self.vote(k, cid, sigil, gen, tid) for k in keys])

    # ------------------------------------------------------------ the run

    def test_every_endpoint_matches(self):
        try:
            self._every_endpoint()
        finally:
            self.report()

    def _every_endpoint(self):
        r, W, S = self.rec, "witness", "standby"
        P, ST, SB = self.plain, self.stamped, self.standby
        cid = self.cid
        tok = {"Authorization": f"Bearer {self.token}"}
        # --- GET endpoints and unknown paths
        for t, role in ((P, W), (ST, W), (SB, S)):
            for path in ("/v0/info", "/v0/charters", "/v0/proofs"):
                r.send(f"{role} GET {path}", t, role, path)
            r.send(f"{role} GET unknown", t, role, "/v0/nope")
            r.send(f"{role} GET root", t, role, "/")
            r.send(f"{role} POST unknown", t, role, "/v0/nope", {})
            r.send(f"{role} POST v1", t, role, "/v1/spend", {})
            r.send(f"{role} GET a POST path", t, role, "/v0/status", method="GET")
        # --- generic cases of every POST endpoint
        for path, fields in (("/v0/spend", ["request"]), ("/v0/release", ["sigil", "proof"]),
                             ("/v0/status", ["sigil"]), ("/v0/sell_stamp", ["blinded"]),
                             ("/v0/heartbeat", ["challenge"]), ("/v0/gossip", ["charters", "proofs", "forks"])):
            r.generic(P, W, path, fields)
        r.generic(ST, W, "/v0/sell_stamp", ["blinded"])
        for path, fields in (("/v0/freeze", ["charter"]), ("/v0/adopt", ["constellation", "version", "snapshots"])):
            r.generic(P, W, path, fields, self.token, admin=True)
        for path, fields in (("/v0/mirror", ["request"]), ("/v0/note_release", ["sigil", "entry"]),
                             ("/v0/gossip", ["charters", "proofs", "forks"])):
            r.generic(SB, S, path, fields)
        for path, fields in (("/v0/standby", ["constellation", "version", "snapshots"]),
                             ("/v0/succeed", ["charter", "sigs"]), ("/v0/probe", ["urls"])):
            r.generic(SB, S, path, fields, self.token, admin=True)
        # --- SPEND: every field of a request missing or of the wrong type
        p0, s0 = self.parcel("aa" * 16)
        T1 = self.hdr([(s0, 0)], "1")
        good = self.req(T1, s0, p0)
        for f in list(good):
            r.send(f"spend request without {f}", P, W, "/v0/spend", {"request": {k: v for k, v in good.items() if k != f}})
            for v in TYPE_FUZZ:
                r.send(f"spend request {f}={json.dumps(v)}", P, W, "/v0/spend", {"request": dict(good, **{f: v})})
        for f in ("sigs", "expires", "preimages", "proofs"):
            r.send(f"spend unlock without {f}", P, W, "/v0/spend",
                   {"request": dict(good, unlock={k: v for k, v in good["unlock"].items() if k != f})})
        # Specific refusals, before anything is bound.
        r.send("spend expired", P, W, "/v0/spend", {"request": self.req(T1, s0, p0, exp=int(time.time()) - 5)})
        r.send("spend wrong signer", P, W, "/v0/spend", {"request": self.req(T1, s0, p0, signer=self.wkeys[0])})
        r.send("spend other home", P, W, "/v0/spend", {"request": dict(good, home="ab" * 32)})
        r.send("spend sigil not in header", P, W, "/v0/spend", {"request": self.req(self.hdr([("cd" * 32, 0)], "1"), s0, p0)})
        r.send("spend duplicate input", P, W, "/v0/spend", {"request": self.req(self.hdr([(s0, 0), (s0, 0)], "1"), s0, p0)})
        r.send("spend gen 16 (cap)", P, W, "/v0/spend", {"request": self.req(self.hdr([(s0, 16)], "1"), s0, p0)}, expect=403)
        r.send("spend negative gen", P, W, "/v0/spend", {"request": self.req(self.hdr([(s0, -1)], "1"), s0, p0)})
        big, sbig = self.parcel("e" * 33_000)
        r.send("spend authorisation over 32 KiB", P, W, "/v0/spend", {"request": self.req(self.hdr([(sbig, 0)], "1"), sbig, big)},
               expect=403)
        r.send("status of the oversized sigil", P, W, "/v0/status", {"sigil": sbig})
        r.send("spend with a stamp field on an unstamped witness", P, W, "/v0/spend", {"request": dict(good, stamp={"x": 1})})
        tl = locks.all_of(locks.sig(self.owner.pk), locks.after(int(time.time()) + 3600))
        ptl, stl = self.parcel("ab" * 16, lock=tl)
        r.send("spend time lock not yet", P, W, "/v0/spend", {"request": self.req(self.hdr([(stl, 0)], "1"), stl, ptl)})
        # Valid votes, a repeat, a conflict, STATUS.
        r.send("spend valid", P, W, "/v0/spend", {"request": good}, expect=200)
        r.send("spend repeat", P, W, "/v0/spend", {"request": good}, expect=200)
        T2 = self.hdr([(s0, 0)], "2")
        r.send("spend conflicting", P, W, "/v0/spend", {"request": self.req(T2, s0, p0)}, expect=409)
        r.send("status bound", P, W, "/v0/status", {"sigil": s0}, expect=200)
        r.send("status unknown", P, W, "/v0/status", {"sigil": "00" * 32}, expect=200)
        r.send("status non-hex", P, W, "/v0/status", {"sigil": "x"})
        r.send("status extra fields", P, W, "/v0/status", {"sigil": s0, "more": [1, 2]})
        # --- RELEASE: a swap whose other input was sealed elsewhere (a valid death proof).
        pa, sa = self.parcel("01" * 16)
        px, sx = self.parcel("02" * 16)
        Tb = self.hdr([(sa, 0), (sx, 0)], "3")       # the dead swap, voted for by this witness
        Ty = self.hdr([(sx, 0)], "4")                # x sealed by Ty instead
        r.send("spend swap input", P, W, "/v0/spend", {"request": self.req(Tb, sa, pa)}, expect=200)
        seal_y = self.seal(self.wkeys[:3], cid, sx, 0, model.transition_id(Ty))
        tgt = {"home": px["home"], "lock": px["lock"], "salt": px["salt"]}
        dp = {"kind": "seal", "sigil": sx, "gen": 0, "parcel": tgt, "seal": seal_y}
        r.send("release bogus proof", P, W, "/v0/release", {"sigil": sa, "proof": {}})
        r.send("release proof of wrong kind", P, W, "/v0/release", {"sigil": sa, "proof": dict(dp, kind="nope")})
        r.send("release proof with a short seal", P, W, "/v0/release",
               {"sigil": sa, "proof": dict(dp, seal=self.seal(self.wkeys[:2], cid, sx, 0, model.transition_id(Ty)))})
        r.send("release proof over 128 KiB", P, W, "/v0/release",
               {"sigil": sa, "proof": dict(dp, pad="x" * (130 * 1024))}, expect=403)
        r.send("release unbound sigil", P, W, "/v0/release", {"sigil": "00" * 32, "proof": dp})
        r.send("release valid", P, W, "/v0/release", {"sigil": sa, "proof": dp}, expect=200)
        r.send("release again", P, W, "/v0/release", {"sigil": sa, "proof": dp})
        r.send("status after release", P, W, "/v0/status", {"sigil": sa}, expect=200)
        r.send("spend at gen 1 after release", P, W, "/v0/spend",
               {"request": self.req(self.hdr([(sa, 1)], "5"), sa, pa)}, expect=200)
        # --- HEARTBEAT
        for ch, name in (("hello", "valid"), ("", "empty"), ("c" * 128, "128 chars"), ("c" * 129, "129 chars"),
                         ("é", "non-ascii")):
            r.send(f"heartbeat {name}", P, W, "/v0/heartbeat", {"challenge": ch})
        # --- STAMPS
        r.send("sell_stamp unstamped", P, W, "/v0/sell_stamp", {"blinded": "abcd"})
        for b, name in (("abcd", "valid"), ("0", "zero"), (format(self.mint_pub["n"] + 1, "x"), "over n"),
                        ("zz", "not hex"), ("-1", "negative"), ("0x10", "0x prefix")):
            r.send(f"sell_stamp {name}", ST, W, "/v0/sell_stamp", {"blinded": b})
        p1, s1 = self.parcel("03" * 16)
        r.send("stamped spend without stamp", ST, W, "/v0/spend", {"request": self.req(self.hdr([(s1, 0)], "6"), s1, p1)})
        r.send("stamped spend junk stamp", ST, W, "/v0/spend",
               {"request": dict(self.req(self.hdr([(s1, 0)], "6"), s1, p1), stamp={"serial": "00", "sig": "01"})})
        from sigil.stamps import buy_stamp
        st = buy_stamp(self.mint_pub, lambda blinded: int(http(ST[1].url, "/v0/sell_stamp",
                                                               {"blinded": format(blinded, "x")})[1]["ok"], 16))
        stamped_req = dict(self.req(self.hdr([(s1, 0)], "6"), s1, p1), stamp=st)
        r.send("stamped spend valid", ST, W, "/v0/spend", {"request": stamped_req}, expect=200)
        r.send("stamped spend stamp reused", ST, W, "/v0/spend", {"request": stamped_req}, expect=403)
        # --- GOSSIP: proofs, chains, forks, caps
        kp0 = self.wkeys[0]
        proof = {"a": self.vote(kp0, cid, "11" * 32, 0, "aa" * 32), "b": self.vote(kp0, cid, "11" * 32, 0, "bb" * 32)}
        forged = {"a": proof["a"], "b": dict(proof["b"], sig=proof["a"]["sig"])}
        r.send("gossip forged proof and junk", P, W, "/v0/gossip", {"proofs": [forged, proof["a"], 5]})
        r.send("gossip proof by an unknown key", P, W, "/v0/gossip",
               {"proofs": [{"a": self.vote(self.owner, cid, "11" * 32, 0, "aa" * 32),
                            "b": self.vote(self.owner, cid, "11" * 32, 0, "bb" * 32)}]})
        r.send("gossip valid proof", P, W, "/v0/gossip", {"proofs": [proof]}, expect=200)
        r.send("gossip same proof again", P, W, "/v0/gossip", {"proofs": [proof]}, expect=200)
        r.send("gossip 65 proofs (cap)", P, W, "/v0/gossip", {"proofs": [proof] * 65}, expect=400)
        r.send("gossip 17 forks (cap)", P, W, "/v0/gossip", {"forks": [{}] * 17}, expect=400)
        r.send("gossip 16 junk forks", P, W, "/v0/gossip", {"forks": [{}] * 16})
        many = {constellation_id(b): [{"body": b, "sigs": {}}]
                for b in ({"name": f"c{i}", "version": 0, "witnesses": ["ab" * 32], "prev": None} for i in range(65))}
        r.send("gossip 65 chains (cap)", P, W, "/v0/gossip", {"charters": many}, expect=400)
        r.send("gossip 64 chains", P, W, "/v0/gossip", {"charters": dict(list(many.items())[:64])}, expect=200)
        for n in (MAX_WITNESSES + 1, MAX_WITNESSES):
            b = {"name": f"big{n}", "version": 0, "witnesses": [f"{i:064x}" for i in range(n)], "prev": None}
            r.send(f"gossip charter of {n} witnesses", P, W, "/v0/gossip",
                   {"charters": {constellation_id(b): [{"body": b, "sigs": {}}]}}, expect=200)
        long_chain = [{"body": {"name": "l", "version": 0, "witnesses": ["ab" * 32], "prev": None}, "sigs": {}}] * 1025
        r.send("gossip chain of 1025 versions (cap)", P, W, "/v0/gossip", {"charters": {"ab" * 32: long_chain}}, expect=400)
        cur = load_json(self.reg)[cid][0]["body"]
        v1 = charter_body(cur["name"], 1, [k.pk for k in self.wkeys[:3]] + [load_key(self.k4).pk], charter_hash(cur))
        v1b = charter_body(cur["name"], 1, [KeyPair.from_seed(bytes([i]) * 32).pk for i in range(4)], charter_hash(cur))
        chain0 = load_json(self.reg)[cid]
        a = {"body": v1, "sigs": {k.pk: sign_charter(k, v1) for k in self.wkeys[:3]}}
        b = {"body": v1b, "sigs": {k.pk: sign_charter(k, v1b) for k in self.wkeys[1:]}}
        r.send("gossip rotation v1", P, W, "/v0/gossip", {"charters": {cid: chain0 + [a]}}, expect=200)
        r.send("gossip conflicting v1 (fork)", P, W, "/v0/gossip", {"charters": {cid: chain0 + [b]}}, expect=200)
        r.send("gossip unsigned v1", P, W, "/v0/gossip", {"charters": {cid: chain0 + [{"body": v1, "sigs": {}}]}})
        r.send("charters after gossip", P, W, "/v0/charters")
        r.send("proofs after gossip", P, W, "/v0/proofs")
        # --- FREEZE (last for the plain twins: irreversible)
        bad_prev = charter_body(cur["name"], 1, ["aa" * 32], "00" * 32)
        r.send("freeze wrong predecessor", P, W, "/v0/freeze", {"charter": bad_prev}, headers=tok)
        r.send("freeze valid", P, W, "/v0/freeze", {"charter": v1}, headers=tok, expect=200)
        r.send("freeze same again", P, W, "/v0/freeze", {"charter": v1}, headers=tok, expect=200)
        r.send("freeze other successor", P, W, "/v0/freeze", {"charter": v1b}, headers=tok, expect=403)
        r.send("info frozen", P, W, "/v0/info")
        r.send("spend when frozen", P, W, "/v0/spend", {"request": good})
        r.send("release when frozen", P, W, "/v0/release", {"sigil": sa, "proof": dp})
        r.send("heartbeat when frozen", P, W, "/v0/heartbeat", {"challenge": "x"})
        r.send("adopt on a joined witness", P, W, "/v0/adopt", {"constellation": cid, "version": 1, "snapshots": []},
               headers=tok)
        # --- ADOPT on a pair of fresh twins started with --adopt (key of v1's member 3)
        AD = self.twin("adopt", self.k4, ["--adopt"])
        for dmn in AD:
            dmn.start()
            self.addCleanup(dmn.stop)
        r.send("adopt info", AD, W, "/v0/info")
        r.send("adopt unknown version", AD, W, "/v0/adopt", {"constellation": cid, "version": 1, "snapshots": []}, headers=tok)
        r.send("adopt spend before adopt", AD, W, "/v0/spend", {"request": good})
        r.send("adopt learns v1", AD, W, "/v0/gossip", {"charters": {cid: chain0 + [a]}}, expect=200)
        r.send("adopt version 0", AD, W, "/v0/adopt", {"constellation": cid, "version": 0, "snapshots": []}, headers=tok)
        r.send("adopt snapshots not a list", AD, W, "/v0/adopt", {"constellation": cid, "version": 1, "snapshots": {}}, headers=tok)
        snap = (http(P[1].url, "/v0/freeze", {"charter": v1}, headers=tok)[1].get("ok") or {}).get("snapshot", {})
        r.send("adopt valid (with junk)", AD, W, "/v0/adopt",
               {"constellation": cid, "version": 1, "snapshots": [snap, 5, {"x": 3}, {s0: [7]}]}, headers=tok, expect=200)
        r.send("adopt retried", AD, W, "/v0/adopt", {"constellation": cid, "version": 1, "snapshots": []}, headers=tok, expect=200)
        r.send("adopt other version", AD, W, "/v0/adopt", {"constellation": cid, "version": 2, "snapshots": []}, headers=tok)
        r.send("adopt inherited status", AD, W, "/v0/status", {"sigil": s0})
        r.send("adopt conflicting spend", AD, W, "/v0/spend", {"request": self.req(T2, s0, p0)}, expect=409)
        # --- STANDBY calls
        hc = self.s["cid"]
        ph, sh = self.parcel("04" * 16, cid=hc)
        mreq = dict(self.req(self.hdr([(sh, 0)], "7"), sh, ph), version=0)
        r.send("mirror without version", SB, S, "/v0/mirror", {"request": {k: v for k, v in mreq.items() if k != "version"}})
        r.send("mirror wrong version", SB, S, "/v0/mirror", {"request": dict(mreq, version=1)})
        r.send("mirror version bool", SB, S, "/v0/mirror", {"request": dict(mreq, version=False)})
        for f in ("sigil", "header", "home", "lock", "salt", "unlock"):
            r.send(f"mirror without {f}", SB, S, "/v0/mirror", {"request": {k: v for k, v in mreq.items() if k != f}})
        r.send("mirror valid", SB, S, "/v0/mirror", {"request": mreq}, expect=200)
        r.send("mirror repeat", SB, S, "/v0/mirror", {"request": mreq}, expect=200)
        for i in range(2, 6):   # transitions 2..5 of (sh, 0): the fifth is refused
            r.send(f"mirror transition {i} at one generation", SB, S, "/v0/mirror",
                   {"request": dict(self.req(self.hdr([(sh, 0)], str(i + 7)), sh, ph), version=0)})
        r.send("mirror gen 16", SB, S, "/v0/mirror", {"request": dict(self.req(self.hdr([(sh, 16)], "7"), sh, ph), version=0)})
        hb, shb = self.parcel("e" * 33_000, cid=hc)
        r.send("mirror over 32 KiB", SB, S, "/v0/mirror", {"request": dict(self.req(self.hdr([(shb, 0)], "7"), shb, hb), version=0)})
        r.send("mirror expired", SB, S, "/v0/mirror",
               {"request": dict(self.req(self.hdr([(sh, 0)], "e"), sh, ph, exp=int(time.time()) - 5), version=0)})
        # note_release: a binding it holds, released by a seal of the sibling input.
        pq, sq = self.parcel("05" * 16, cid=hc)
        Tsw = self.hdr([(sh, 0), (sq, 0)], "7")
        r.send("mirror swap", SB, S, "/v0/mirror", {"request": dict(self.req(Tsw, sh, ph), version=0)})
        Tq = self.hdr([(sq, 0)], "f")
        dpq = {"kind": "seal", "sigil": sq, "gen": 0, "parcel": {"home": hc, "lock": pq["lock"], "salt": pq["salt"]},
               "seal": self.seal(self.skeys[:3], hc, sq, 0, model.transition_id(Tq))}
        entry = {"kind": "release", "gen": 0, "tid": model.transition_id(Tsw), "header": Tsw, "proof": dpq}
        r.send("note_release junk entry", SB, S, "/v0/note_release", {"sigil": sh, "entry": {"kind": "release"}})
        r.send("note_release proof over 128 KiB", SB, S, "/v0/note_release",
               {"sigil": sh, "entry": dict(entry, proof=dict(dpq, pad="x" * (130 * 1024)))})
        r.send("note_release unknown binding", SB, S, "/v0/note_release", {"sigil": "00" * 32, "entry": entry})
        r.send("note_release valid", SB, S, "/v0/note_release", {"sigil": sh, "entry": entry})
        r.send("note_release again", SB, S, "/v0/note_release", {"sigil": sh, "entry": entry})
        # probe: no URLs, a dead URL, the heir witnesses (alive).
        r.send("probe no urls", SB, S, "/v0/probe", {"urls": []}, headers=tok, expect=200)
        r.send("probe urls not strings", SB, S, "/v0/probe", {"urls": [5]}, headers=tok)
        r.send("probe dead url", SB, S, "/v0/probe", {"urls": ["http://127.0.0.1:9"]}, headers=tok, expect=200)
        r.send("probe default members", SB, S, "/v0/probe", {}, headers=tok, expect=200)
        # succeed: a malformed charter, a non-successor, a live version (refused), cooperative (signed).
        hcur = load_json(self.s["registry"])[hc][0]["body"]
        nxt = charter_body(hcur["name"], 1, [k.pk for k in self.skeys], charter_hash(hcur))
        r.send("succeed malformed charter", SB, S, "/v0/succeed", {"charter": {"x": 1}}, headers=tok)
        r.send("succeed wrong predecessor", SB, S, "/v0/succeed", {"charter": dict(nxt, prev="00" * 32)}, headers=tok)
        r.send("succeed alive without sigs", SB, S, "/v0/succeed", {"charter": nxt}, headers=tok)
        r.send("succeed sigs not an object", SB, S, "/v0/succeed", {"charter": nxt, "sigs": [1]}, headers=tok)
        r.send("succeed too few sigs", SB, S, "/v0/succeed",
               {"charter": nxt, "sigs": {k.pk: sign_charter(k, nxt) for k in self.skeys[:2]}}, headers=tok)
        sigs = {k.pk: sign_charter(k, nxt) for k in self.skeys[:3]}
        r.send("succeed cooperative", SB, S, "/v0/succeed", {"charter": nxt, "sigs": sigs}, headers=tok, expect=200)
        r.send("succeed same again", SB, S, "/v0/succeed", {"charter": nxt, "sigs": sigs}, headers=tok, expect=200)
        other = charter_body(hcur["name"], 1, [k.pk for k in self.ckeys], charter_hash(hcur))
        r.send("succeed other successor", SB, S, "/v0/succeed",
               {"charter": other, "sigs": {k.pk: sign_charter(k, other) for k in self.skeys[:3]}}, headers=tok, expect=403)
        r.send("standby info fenced", SB, S, "/v0/info")
        r.send("mirror when fenced", SB, S, "/v0/mirror", {"request": mreq}, expect=403)
        r.send("standby entry when standing by", SB, S, "/v0/standby",
               {"constellation": hc, "version": 1, "snapshots": []}, headers=tok)
        # --- the heir witnesses: a vote needs mirror acks
        r.send("heir spend without acks", self.heirw, W, "/v0/spend", {"request": self.req(self.hdr([(sh, 0)], "7"), sh, ph)})
        r.send("heir spend junk acks", self.heirw, W, "/v0/spend",
               {"request": dict(self.req(self.hdr([(sh, 0)], "7"), sh, ph), mirror=[{"x": 1}, 5])})
        r.send("heir spend acks not a list", self.heirw, W, "/v0/spend",
               {"request": dict(self.req(self.hdr([(sh, 0)], "7"), sh, ph), mirror={"x": 1})})
        # --- coverage: every WIRE.md endpoint got cases
        listed = wire_endpoints()
        self.assertGreaterEqual(len(listed), 17, listed)
        missing = sorted(set(listed) - r.covered)
        self.assertEqual(missing, [], f"WIRE.md endpoints without a generated case: {missing}")

    def test_rate_limit_matches(self):
        """429 with the same body and a Retry-After header, after the same burst, on both twins."""
        L = self.limited
        for d in L:
            codes, last = [], None
            for _ in range(6):
                code, body, hdrs = http(d.url, "/v0/status", {"sigil": "00" * 32})
                codes.append(code)
                if code == 429:
                    last = (body, int(hdrs.get("retry-after", "0")) >= 1)
            self.assertEqual(codes[:3], [200, 200, 200], (d.kind, codes))
            self.assertGreaterEqual(codes.count(429), 2, (d.kind, codes))
            self.assertEqual(last, ({"error": "rejected", "message": "rate limited", "vote": None}, True), d.kind)
            # Operator calls are never limited: the token decides.
            code, body, _ = http(d.url, "/v0/freeze", {})
            self.assertEqual((code, body["message"]), (403, "bad admin token"), d.kind)
            # GET endpoints are charged too.
            self.assertEqual(http(d.url, "/v0/info")[0], 429, d.kind)

    def report(self):
        r = self.rec
        if getattr(self, "_reported", False):
            return
        self._reported = True
        lines = [f"{r.cases} cases sent to each twin; {len(r.diffs)} differences, {len(r.soft)} known, "
                 f"{len(r.messages)} bad_request messages worded differently"]
        for d in r.diffs:
            lines.append("  " + json.dumps(d, default=str)[:600])
        for s in r.soft:
            lines.append("  (known) " + json.dumps(s, default=str)[:300])
        out = os.environ.get("SIGIL_WIRE_OUT")
        if out:
            with open(out, "w") as f:
                json.dump({"cases": r.cases, "diffs": r.diffs, "known": r.soft, "bad_request_messages": r.messages}, f, indent=1, default=str)
        self.assertEqual(r.diffs, [], "\n".join(lines))


if __name__ == "__main__":
    unittest.main()
