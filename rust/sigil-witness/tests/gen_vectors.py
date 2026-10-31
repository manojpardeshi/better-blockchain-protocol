"""Generate golden test vectors for the Rust witness from the Python reference.

    PYTHONPATH=. python3 rust/sigil-witness/tests/gen_vectors.py > rust/sigil-witness/tests/vectors.json

Everything is deterministic (fixed seeds, a fixed clock, Ed25519's deterministic
signatures, and a seeded RNG), so re-running produces the same file as long as the
reference behaves the same. The Rust tests (tests/vectors.rs) check that the Rust
implementation produces byte-identical encodings, hashes, signatures and votes, and the
same accept/reject verdicts.

Where the Rust witness is deliberately stricter than the reference, a vector carries
``"rust": <expected>`` next to the reference's ``"python": <verdict>``.
"""

import json
import math
import random
import struct
import sys
from dataclasses import asdict

from sigil import locks, model
from sigil.charter import Registry, charter_body, charter_hash, constellation_id, sign_charter
from sigil.gossip import GossipStore
from sigil.crypto import KeyPair, verify
from sigil.encoding import canonical, digest
from sigil.locks import evaluate, well_formed
from sigil.proofs import proves_dead, verify_equivocation, verify_seal
from sigil.witness import Conflict, Rejected, Witness

rng = random.Random(20261023)


def kp(i: int) -> KeyPair:
    return KeyPair.from_seed(f"sigil-vector-{i}".encode())


# ------------------------------------------------------------- canonical JSON

def canonical_cases() -> list:
    texts = [
        '{"b":[1,2.5,null,true,false],"a":"x"}', '"\\u00e9\\ud83d\\ude00 tab\\t nl\\n cr\\r bs\\b ff\\f \\u0001 \\u007f"',
        '"\\"quoted\\" back\\\\slash /slash \\/"', '"日本語 Ελληνικά ☃ 𝄞"', '-0', '0', '-1', '123456789012345678901234567890',
        '-170141183460469231731687303715884105728', '170141183460469231731687303715884105727',
        '1E5', '1e16', '1e15', '1e-5', '1e-4', '0.1', '0.30000000000000004', '1e22', '1e21', '100.0', '-0.0',
        '1234567890123456.7', '12345678901234567.0', '5e-324', '2.5e-320', '1.7976931348623157e308', '1.5e300',
        '123.456e7', '9007199254740993', '9007199254740993.0', '1e-7', '0.000123', '[]', '{}', '[[[]]]',
        '{"a":1,"a":2}', '{"z":{"y":{"x":[{"b":1,"a":2}]}}}', '{"\\u00e9":1,"e":2,"f":3,"\\ud83d\\ude00":4,"~":5}',
        ' \t\n\r{ "k" : [ 1 , 2 ] } ', '"\\u0000"', '"\\u2028\\u2029"', 'true', 'null',
    ]
    for _ in range(1500):
        bits = rng.getrandbits(64)
        x = struct.unpack("<d", struct.pack("<Q", bits))[0]
        if math.isfinite(x):
            texts.append(repr(x))
    for _ in range(250):
        texts.append(f"{rng.randint(-10**6, 10**6)}.{rng.randint(0, 10**9):09d}e{rng.randint(-30, 30)}")
        texts.append(repr(rng.uniform(-1e3, 1e3)))
        texts.append(str(rng.randint(-2**100, 2**100)))
    alphabet = [chr(c) for c in list(range(0, 0x80)) + [0xe9, 0x2028, 0xfeff, 0xffff, 0x10000, 0x1f600, 0x10ffff]]
    for _ in range(300):
        s = "".join(rng.choice(alphabet) for _ in range(rng.randint(0, 12)))
        texts.append(json.dumps({s: [s, rng.randint(-5, 5)]}, ensure_ascii=bool(rng.getrandbits(1))))
    out = []
    for t in texts:
        v = json.loads(t)
        out.append({"json": t, "canonical": canonical(v).decode(), "digest": digest("test", v)})
    return out


# ---------------------------------------------------------- keys & signatures

def key_cases() -> list:
    out = []
    for i in range(8):
        k = kp(i)
        obj = {"i": i, "msg": "vote me", "u": "é\U0001f600"}
        out.append({"py_seed": f"sigil-vector-{i}".encode().hex(), "pk": k.pk,
                    "obj": obj, "sig": k.sign("vote", obj), "unlock_sig": locks.sign_unlock(k, "s" * 64, "t" * 64, 1700000000 + i)})
    return out


def model_cases() -> list:
    out = []
    for i in range(5):
        k = kp(i)
        lock = locks.sig(k.pk) if i % 2 == 0 else locks.multi(1, [k.pk, kp(i + 10).pk])
        p = {"home": "c" * 64, "lock": lock, "salt": f"{i:032x}"}
        b = model.body([model.ref("a" * 64, i)], [model.parcel("c" * 64, "asset", 5 + i, lock, "ff" * 16)], memo="mé")
        h = model.header([[model.sigil_of(p), i]], b)
        out.append({"parcel": p, "sigil": model.sigil_of(p), "body": b, "body_hash": model.body_hash(b),
                    "header": h, "tid": model.transition_id(h)})
    return out


# ------------------------------------------------------------------ locks

def lock_cases() -> list:
    a, b, c = kp(1), kp(2), kp(3)
    S, T = "s" * 64, "t" * 64
    pre = "0123456789abcdef"
    h = __import__("sigil.encoding", fromlist=["hash_preimage"]).hash_preimage(pre)

    def u(*signers, expires=1700000100, pre_map=None, eq=None, msg_expires=None):
        x = locks.empty_unlock(expires)
        for k in signers:
            x["sigs"][k.pk] = locks.sign_unlock(k, S, T, expires if msg_expires is None else msg_expires)
        x["preimages"] = pre_map or {}
        x["equivocations"] = eq or []
        return x

    # an equivocation proof against witness c
    va = {"constellation": "C", "version": 0, "witness": c.pk, "sigil": "q", "gen": 0, "tid": "t1", "time": 1}
    vb = dict(va, tid="t2")
    va["sig"] = c.sign("vote", model.vote_payload(va))
    vb["sig"] = c.sign("vote", model.vote_payload(vb))
    eq = {"a": va, "b": vb}
    bad_eq = {"a": va, "b": dict(vb, sig=va["sig"])}

    deep = locks.sig(a.pk)
    for _ in range(9):
        deep = locks.all_of(deep)
    wide = locks.any_of(*[locks.sig(a.pk)] * 64)
    cases = [
        (locks.sig(a.pk), u(a)), (locks.sig(a.pk), u(b)), (locks.sig(a.pk), u(a, msg_expires=1)),
        (locks.multi(2, [a.pk, b.pk, c.pk]), u(a, c)), (locks.multi(2, [a.pk, b.pk, c.pk]), u(b)),
        (locks.multi(0, [a.pk]), u(a)), ({"op": "multi", "k": True, "pks": [a.pk]}, u(a)),
        (locks.multi(1, [a.pk, a.pk]), u(a)), (locks.after(1700000050), u()), (locks.before(1700000050), u()),
        (locks.all_of(locks.sig(a.pk), locks.after(1700000050)), u(a)),
        (locks.any_of(locks.sig(b.pk), locks.before(1700000050)), u()),
        (locks.hashlock(h), u(pre_map={h: pre})), (locks.hashlock(h), u(pre_map={h: "00"})),
        (locks.hashlock(h), u(pre_map={h: "zz"})), (locks.hashlock(h.upper()), u(pre_map={h.upper(): pre})),
        (locks.equivocation(c.pk), u(eq=[eq])), (locks.equivocation(c.pk), u(eq=[bad_eq])),
        (locks.equivocation(a.pk), u(eq=[eq])), (locks.never(), u(a)), ({"op": "never", "x": 1}, u()),
        ({"op": "sig", "pk": a.pk, "extra": 1}, u(a)), ({"op": "after", "t": True}, u()), ({"op": "all", "of": []}, u()),
        (deep, u(a)), (wide, u(a)), (locks.any_of(*[locks.sig(a.pk)] * 63), u(a)), ("not a lock", u()),
        (locks.sig(a.pk), "not an unlock"), (locks.sig(a.pk), {"sigs": [], "expires": 1700000100}),
        (locks.sig(a.pk), dict(u(a), expires=None)), (locks.sig(a.pk), {k: v for k, v in u(a).items() if k != "expires"}),
        (locks.all_of(locks.multi(1, [a.pk]), locks.any_of(locks.sig(b.pk), locks.sig(a.pk))), u(a)),
        # MAX_EQUIVOCATIONS: an unlock with more proofs than any lock could need satisfies nothing.
        (locks.equivocation(c.pk), u(eq=[eq] * locks.MAX_EQUIVOCATIONS)),
        (locks.equivocation(c.pk), u(eq=[eq] * (locks.MAX_EQUIVOCATIONS + 1))),
        (locks.any_of(locks.sig(a.pk), locks.equivocation(c.pk)), u(a, eq=[bad_eq] * (locks.MAX_EQUIVOCATIONS + 1))),
        # MAX_KEYS: a lock names at most 64 keys in all (sig and multi), bounding signature checks.
        (locks.multi(1, [a.pk] + [kp(100 + i).pk for i in range(locks.MAX_KEYS - 1)]), u(a)),
        (locks.multi(1, [a.pk] + [kp(100 + i).pk for i in range(locks.MAX_KEYS)]), u(a)),
        (locks.any_of(locks.sig(a.pk), locks.multi(1, [kp(100 + i).pk for i in range(locks.MAX_KEYS)])), u(a)),
    ]
    out = []
    for lock, unlock in cases:
        verdicts = {str(now): evaluate(lock, unlock, S, T, now) for now in (None, 1700000000, 1700000050, 1700000100)}
        out.append({"lock": lock, "unlock": unlock, "sigil": S, "tid": T, "well_formed": well_formed(lock),
                    "eval": verdicts})
    return out


# ----------------------------------------------------- charters, seals, proofs

def constellation(name: str, base: int, n: int):
    keys = [kp(base + i) for i in range(n)]
    body = charter_body(name, 0, [k.pk for k in keys], None)
    return keys, constellation_id(body), [{"body": body, "sigs": {}}]


def vote(k, cid, sigil, gen, tid, t=1700000000, version=0):
    v = {"constellation": cid, "version": version, "witness": k.pk, "sigil": sigil, "gen": gen, "tid": tid, "time": t}
    v["sig"] = k.sign("vote", model.vote_payload(v))
    return v


def proof_cases():
    keys, X, chainX = constellation("orion", 100, 4)
    ekeys, E, chainE = constellation("evil", 200, 4)
    reg = Registry()
    reg.add_chain(X, chainX)
    reg.add_chain(E, chainE)
    owner = kp(300)
    p = {"home": X, "lock": locks.sig(owner.pk), "salt": "ab" * 16}
    s = model.sigil_of(p)
    body = model.body([model.ref("0" * 64, 0)], [model.parcel(X, "a", 1, p["lock"], "cd" * 16)])
    hdr = model.header([[s, 0]], body)
    tid = model.transition_id(hdr)
    other = "e" * 64
    votes_other = [vote(k, X, s, 0, other) for k in keys]
    seal_other = model.seal_from_votes(votes_other[:3])
    votes_tid = [vote(k, X, s, 0, tid) for k in keys]
    real_seal = model.seal_from_votes(votes_tid)

    seals = [
        ("valid quorum", seal_other), ("all four", model.seal_from_votes(votes_other)),
        ("below quorum", model.seal_from_votes(votes_other[:2])),
        ("duplicate voter", model.seal_from_votes([votes_other[0], votes_other[0], votes_other[1]])),
        ("bad signature", dict(seal_other, votes=[dict(seal_other["votes"][0], sig=seal_other["votes"][1]["sig"])]
                               + seal_other["votes"][1:])),
        ("unknown version", dict(seal_other, version=1)), ("unknown constellation", dict(seal_other, constellation="x")),
        ("wrong tid", dict(seal_other, tid=tid)), ("non-dict entry", dict(seal_other, votes=seal_other["votes"] + [5])),
        ("empty", dict(seal_other, votes=[])),
        ("bad sig then good duplicate", dict(seal_other, votes=[dict(seal_other["votes"][0], sig="00" * 64)]
                                             + seal_other["votes"])),
        # The reference lets entry keys override the seal's fields (see proofs.rs): Rust refuses.
        ("entry overrides tid", dict(real_seal, tid=other, votes=[dict(e, tid=tid) for e in real_seal["votes"]]), False),
        ("entry overrides constellation", {"constellation": X, "version": 0, "sigil": s, "gen": 0, "tid": other, "votes": [
            {"witness": v["witness"], "time": v["time"], "sig": v["sig"], "constellation": E}
            for v in (vote(k, E, s, 0, other) for k in ekeys)]}, False),
    ]
    seal_out = []
    for case in seals:
        name, seal = case[0], case[1]
        py = verify_seal(seal, reg)
        entry = {"name": name, "seal": seal, "python": py}
        if len(case) > 2:
            entry["rust"] = case[2]
        seal_out.append(entry)
    conv = {"name": "convicted voter", "seal": seal_other, "convicted": [keys[0].pk],
            "python": verify_seal(seal_other, reg, {keys[0].pk})}
    seal_out.append(conv)

    eqs = [
        ("valid", {"a": votes_other[0], "b": votes_tid[0]}),
        ("same tid", {"a": votes_other[0], "b": votes_other[0]}),
        ("different witness", {"a": votes_other[0], "b": votes_tid[1]}),
        ("different gen", {"a": votes_other[0], "b": vote(keys[0], X, s, 1, tid)}),
        ("bad sig", {"a": votes_other[0], "b": dict(votes_tid[0], sig=votes_other[0]["sig"])}),
        ("missing b", {"a": votes_other[0]}),
    ]
    eq_out = [{"name": n, "proof": pr, "python": verify_equivocation(pr)} for n, pr in eqs]

    parcel = {"home": X, "lock": p["lock"], "salt": p["salt"]}
    deaths = [
        ("seal kind", {"kind": "seal", "sigil": s, "gen": 0, "parcel": parcel, "seal": seal_other}),
        ("votes kind", {"kind": "votes", "sigil": s, "gen": 0, "parcel": parcel, "votes": votes_other[1:]}),
        ("votes below quorum", {"kind": "votes", "sigil": s, "gen": 0, "parcel": parcel, "votes": votes_other[2:]}),
        ("own seal", {"kind": "seal", "sigil": s, "gen": 0, "parcel": parcel, "seal": real_seal}),
        ("wrong gen", {"kind": "seal", "sigil": s, "gen": 1, "parcel": parcel, "seal": dict(seal_other, gen=1)}),
        ("wrong parcel", {"kind": "seal", "sigil": s, "gen": 0, "parcel": dict(parcel, salt="00"), "seal": seal_other}),
        ("foreign home", {"kind": "seal", "sigil": s, "gen": 0, "parcel": parcel,
                          "seal": model.seal_from_votes([vote(k, E, s, 0, other) for k in ekeys])}),
        ("votes include target tid", {"kind": "votes", "sigil": s, "gen": 0, "parcel": parcel,
                                      "votes": votes_other[1:] + [votes_tid[0]]}),
        ("unknown kind", {"kind": "maybe", "sigil": s, "gen": 0, "parcel": parcel, "seal": seal_other}),
        ("override attack", {"kind": "seal", "sigil": s, "gen": 0, "parcel": parcel,
                             "seal": dict(real_seal, tid=other, votes=[dict(e, tid=tid) for e in real_seal["votes"]])},
         False),
    ]
    death_out = []
    for case in deaths:
        entry = {"name": case[0], "proof": case[1], "python": proves_dead(hdr, tid, case[1], reg)}
        if len(case) > 2:
            entry["rust"] = case[2]
        death_out.append(entry)
    return {"registry": {X: chainX, E: chainE}, "header": hdr, "tid": tid,
            "seals": seal_out, "equivocations": eq_out, "deaths": death_out}


# ------------------------------------------------------ a scripted witness run

def witness_script():
    """Drive a reference witness through spends and releases; record every answer."""
    keys, X, chainX = constellation("lyra", 400, 4)
    _, Y, chainY = constellation("vega", 500, 4)
    reg = Registry()
    reg.add_chain(X, chainX)
    reg.add_chain(Y, chainY)
    clock = [1700000000]
    w = Witness(keys[0], reg, lambda: clock[0])
    w.join(X, 0)
    owner, owner2, ow3 = kp(600), kp(601), kp(602)
    steps = []

    def run(op, now, *args):
        clock[0] = now
        try:
            res = getattr(w, op)(*args)
            out = {"ok": res}
        except Conflict as e:
            out = {"error": "conflict", "vote": e.vote}
        except Rejected as e:
            out = {"error": "rejected", "message": str(e)}
        except (ValueError, KeyError, TypeError, AttributeError) as e:
            out = {"error": "bad_request"}
        steps.append({"op": op, "now": now, "args": list(args), "expect": out})
        return out

    def spend_req(parcel, inputs, signers, expires=1700000600, memo="", extra=None, sigil=None, hx=None):
        b = model.body([model.ref("1" * 64, i) for i in range(len(inputs))], [model.parcel(X, "a", 1, locks.sig(owner.pk), "ee" * 16)], memo=memo)
        h = model.header(inputs, b)
        h.update(hx or {})
        t = model.transition_id(h)
        s = sigil or model.sigil_of(parcel)
        u = locks.empty_unlock(expires)
        for k in signers:
            u["sigs"][k.pk] = locks.sign_unlock(k, s, t, expires)
        u.update(extra or {})
        req = {"sigil": s, "header": h, "home": parcel["home"], "lock": parcel["lock"], "salt": parcel["salt"], "unlock": u}
        return req, h, t

    p1 = {"home": X, "lock": locks.sig(owner.pk), "salt": "01" * 16}
    s1 = model.sigil_of(p1)
    r1, h1, t1 = spend_req(p1, [[s1, 0]], [owner])
    r1b, h1b, t1b = spend_req(p1, [[s1, 0]], [owner], memo="other")
    run("spend", 1700000001, r1)                       # vote
    run("spend", 1700000005, r1)                       # same vote again (time unchanged)
    run("spend", 1700000006, r1b)                      # conflict, carries the first vote
    run("status", 1700000007, s1)
    # A two-input transition whose other input (in Y) is sealed elsewhere: dead, so releasable.
    p2 = {"home": X, "lock": locks.sig(owner.pk), "salt": "02" * 16}
    s2 = model.sigil_of(p2)
    q = {"home": Y, "lock": locks.sig(owner2.pk), "salt": "03" * 16}
    sq = model.sigil_of(q)
    r2, h2, t2 = spend_req(p2, [[s2, 0], [sq, 0]], [owner])
    run("spend", 1700000010, r2)
    ykeys = [kp(500 + i) for i in range(4)]
    dead_seal = model.seal_from_votes([vote(k, Y, sq, 0, "9" * 64) for k in ykeys[:3]])
    death = {"kind": "seal", "sigil": sq, "gen": 0, "parcel": q, "seal": dead_seal}
    forged = {"kind": "seal", "sigil": s2, "gen": 0, "parcel": p2, "seal": model.seal_from_votes([vote(k, Y, s2, 0, "9" * 64) for k in ykeys[:3]])}
    run("release", 1700000011, s2, forged)             # evidence not from the target's home: rejected
    run("release", 1700000012, s2, death)              # -> gen 1
    run("release", 1700000013, s2, death)              # nothing bound any more
    r3, _, _ = spend_req(p2, [[s2, 0]], [owner], memo="again")
    run("spend", 1700000014, r3)                       # stale generation
    r4, _, _ = spend_req(p2, [[s2, 1]], [owner], memo="gen1")
    run("spend", 1700000015, r4)                       # vote at gen 1
    run("status", 1700000016, s2)
    # gen skipping, expiry, time locks, hash locks, multisig, equivocation locks
    p5 = {"home": X, "lock": locks.sig(owner.pk), "salt": "05" * 16}
    s5 = model.sigil_of(p5)
    run("spend", 1700000020, spend_req(p5, [[s5, 3]], [owner])[0])
    p6 = {"home": X, "lock": locks.sig(owner.pk), "salt": "06" * 16}
    s6 = model.sigil_of(p6)
    run("spend", 1700000700, spend_req(p6, [[s6, 0]], [owner], expires=1700000600)[0])   # expired
    run("spend", 1700000600, spend_req(p6, [[s6, 0]], [owner], expires=1700000600)[0])   # exactly at expiry: ok
    p7 = {"home": X, "lock": locks.all_of(locks.sig(owner.pk), locks.after(1700000100)), "salt": "07" * 16}
    s7 = model.sigil_of(p7)
    r7 = spend_req(p7, [[s7, 0]], [owner])[0]
    run("spend", 1700000050, r7)                       # not yet
    run("spend", 1700000100, r7)                       # now
    from sigil.encoding import hash_preimage
    pre = "c0ffee"
    p8 = {"home": X, "lock": locks.any_of(locks.hashlock(hash_preimage(pre)), locks.multi(2, [owner.pk, owner2.pk, ow3.pk])), "salt": "08" * 16}
    s8 = model.sigil_of(p8)
    run("spend", 1700000030, spend_req(p8, [[s8, 0]], [owner])[0])                         # 1 of 2: no
    run("spend", 1700000031, spend_req(p8, [[s8, 0]], [owner, ow3])[0])                    # 2 of 3
    p9 = {"home": X, "lock": locks.hashlock(hash_preimage(pre)), "salt": "09" * 16}
    s9 = model.sigil_of(p9)
    run("spend", 1700000032, spend_req(p9, [[s9, 0]], [], extra={"preimages": {hash_preimage(pre): pre}})[0])
    bond_w = kp(700)
    pa = {"home": X, "lock": locks.equivocation(bond_w.pk), "salt": "0a" * 16}
    sa = model.sigil_of(pa)
    eq = {"a": vote(bond_w, Y, "z", 0, "t1"), "b": vote(bond_w, Y, "z", 0, "t2")}
    run("spend", 1700000033, spend_req(pa, [[sa, 0]], [], extra={"equivocations": [{"a": eq["a"], "b": eq["a"]}]})[0])
    run("spend", 1700000034, spend_req(pa, [[sa, 0]], [], extra={"equivocations": [eq]})[0])
    # malformed requests
    pb = {"home": X, "lock": locks.sig(owner.pk), "salt": "0b" * 16}
    sb = model.sigil_of(pb)
    good, hb, tb = spend_req(pb, [[sb, 0]], [owner])
    run("spend", 1700000040, dict(good, home=Y))                                           # wrong home
    run("spend", 1700000040, dict(good, salt="00"))                                        # sigil mismatch
    run("spend", 1700000040, dict(good, unlock=None))                                      # AttributeError: 400
    run("spend", 1700000040, dict(good, unlock=dict(good["unlock"], expires=True)))        # bool expires
    run("spend", 1700000040, dict(good, unlock=dict(good["unlock"], expires=1700000601)))  # signed other expiry
    run("spend", 1700000040, dict(good, header=dict(hb, inputs=[[sb, 0], [sb, 0]])))       # duplicate sigil
    run("spend", 1700000040, dict(good, header=dict(hb, inputs=[[sb, -1]])))               # negative gen
    run("spend", 1700000040, dict(good, header=dict(hb, inputs=[[sb, 0], ["x", 0]], extra=[1.5, "é"])))  # extra header keys: hashed as given
    run("spend", 1700000040, "not a request")
    pc = {"home": X, "lock": locks.sig(owner.pk), "salt": "0c" * 16}
    sc = model.sigil_of(pc)
    run("spend", 1700000043, spend_req(pc, [[sc, 0]], [owner], hx={"x": [1.5, 1e16, -0.0, 5e-324, "\u00e9\U0001f600", {"b": 1, "a": None}]})[0])
    run("spend", 1700000041, good)
    run("status", 1700000042, "unknown")
    return {"registry": {X: chainX, Y: chainY}, "cid": X, "key_py_seed": "sigil-vector-400".encode().hex(), "steps": steps}


# --------------------------------------------- multi-witness scripts (rotation, stamps, gossip)

class Script:
    """Scripted calls on several named reference witnesses; every answer is recorded.

    ``witnesses`` describes how the Rust side builds each one: its key seed, which registry it
    starts from, whether it waits for ADOPT, and whether it sells stamps.
    """

    def __init__(self, clock: list):
        self.clock = clock
        self.ws: dict = {}
        self.gossip: dict = {}
        self.spec: dict = {}
        self.steps: list = []

    def add(self, who: str, w: Witness, seed: int, registry: str, adopt: bool = False, stamps: bool = False):
        self.ws[who] = w
        self.spec[who] = {"py_seed": f"sigil-vector-{seed}".encode().hex(), "registry": registry,
                          "adopt": adopt, "stamps": stamps}
        return w

    def run(self, who: str, op: str, now: int, *args):
        self.clock[0] = now
        w = self.ws[who]
        try:
            if op == "freeze":
                sig, snap = w.freeze(*args)
                res = {"sig": sig, "snapshot": snap}
            elif op == "adopt":
                w.adopt(*args)
                res = {"constellation": w.cid, "version": w.version}  # what /v0/adopt answers
            elif op == "record":
                r = w.records.get(args[0])
                res = asdict(r) if r is not None else None
            elif op == "sell_stamp":
                res = format(w.sell_stamp(int(args[0], 16)), "x")
            elif op == "gossip":
                g = self.gossip.setdefault(who, GossipStore(w.registry))
                res = g.merge(args[0])
            elif op == "proofs":
                g = self.gossip.setdefault(who, GossipStore(w.registry))
                res = {"proofs": list(g.proofs.values()), "forks": list(g.forks.values())}
            elif op == "charters":
                res = {cid: w.registry.chain(cid) for cid in w.registry.ids()}
            else:
                res = getattr(w, op)(*args)
            out = {"ok": res}
        except Conflict as e:
            out = {"error": "conflict", "vote": e.vote}
        except Rejected as e:
            out = {"error": "rejected", "message": str(e)}
        except (ValueError, KeyError, TypeError, AttributeError):
            out = {"error": "bad_request"}
        # A deep copy: later calls must not change what this step recorded.
        self.steps.append(json.loads(json.dumps({"who": who, "op": op, "now": now, "args": list(args), "expect": out})))
        return out

    def done(self, **extra) -> dict:
        return dict(extra, witnesses=self.spec, steps=self.steps)


def rotation_script():
    """FREEZE on an old member, ADOPT on a new and a re-used key, then RELEASE of CONTESTED records.

    Old charter X v0 = o0..o3; v1 = n1, n2, n3 and the re-used key of o3. The owner equivocates
    on two sigils, and one sigil replays the two rotation regressions of
    tests/test_conformance.py (RotationRegressionTests). Only o0, n1 and r3 (o3's key in v1)
    are replayed by the Rust test; o1..o3 provide seals and snapshots.
    """
    old = [kp(800 + i) for i in range(4)]
    new = [kp(810), kp(811), kp(812), old[3]]
    body0 = charter_body("rot", 0, [k.pk for k in old], None)
    X = constellation_id(body0)
    chain0 = [{"body": body0, "sigs": {}}]
    reg0 = Registry()
    reg0.add_chain(X, chain0)
    clock = [1700000000]
    sc = Script(clock)
    o = [Witness(k, reg0, lambda: clock[0]) for k in old]
    for w in o:
        w.join(X, 0)
    sc.add("o0", o[0], 800, "v0")
    owner = kp(850)
    exp = 1700000000 + 10 ** 6

    def mk(salt):
        p = {"home": X, "lock": locks.sig(owner.pk), "salt": salt}
        return p, model.sigil_of(p)

    def hdr(inputs, tag):
        return {"inputs": [list(i) for i in inputs], "body": tag * 32}

    def req(h, sigil, p):
        u = locks.empty_unlock(exp)
        u["sigs"][owner.pk] = locks.sign_unlock(owner, sigil, model.transition_id(h), exp)
        return {"sigil": sigil, "header": h, "home": X, "lock": p["lock"], "salt": p["salt"], "unlock": u}

    def tgt(p):
        return {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}

    t = [1700000100]

    def spend(i, h, sigil, p):
        """o[i] votes; o0's calls are recorded steps."""
        t[0] += 1
        if i == 0:
            return sc.run("o0", "spend", t[0], req(h, sigil, p)).get("ok")
        clock[0] = t[0]
        return o[i].spend(req(h, sigil, p))

    def release(i, sigil, proof):
        t[0] += 1
        if i == 0:
            return sc.run("o0", "release", t[0], sigil, proof)
        clock[0] = t[0]
        return o[i].release(sigil, proof)

    pA, sA = mk("aa")
    pB, sB = mk("bb")
    pC, sC = mk("cc")
    pxC, xC = mk("cx")
    pD, sD = mk("dd")
    pxD, xD = mk("dx")
    pF, sF = mk("ff")
    pG, sG = mk("99")
    TA = hdr([(sA, 0)], "a1")
    TB1, TB2 = hdr([(sB, 0)], "b1"), hdr([(sB, 0)], "b2")
    TC, TyC, TC1 = hdr([(sC, 0), (xC, 0)], "c1"), hdr([(xC, 0)], "c2"), hdr([(sC, 1)], "c3")
    Ty, Tb, Ta, Tg = hdr([(xD, 0)], "d1"), hdr([(sD, 0), (xD, 0)], "d2"), hdr([(sD, 0)], "d3"), hdr([(sD, 1)], "d4")
    TF, TG = hdr([(sF, 2)], "f1"), hdr([(sG, 0)], "e1")

    for i in range(4):
        spend(i, TA, sA, pA)                                   # A: a lone binding everywhere
    for i in range(3):
        spend(i, TB1, sB, pB)                                  # B: the owner equivocates at gen 0
    spend(3, TB2, sB, pB)
    spend(0, TB2, sB, pB)                                      # o0: conflict carrying its vote
    seal_yC = model.seal_from_votes([spend(i, TyC, xC, pxC) for i in range(4)])
    for i in range(4):                                         # C: bound, released, re-bound at gen 1
        spend(i, TC, sC, pC)
    dpC = {"kind": "seal", "sigil": xC, "gen": 0, "parcel": tgt(pxC), "seal": seal_yC}
    for i in range(4):
        release(i, sC, dpC)
    for i in range(2):
        spend(i, TC1, sC, pC)
    seal_y = model.seal_from_votes([spend(i, Ty, xD, pxD) for i in range(4)])   # D: the regression
    seal_b = model.seal_from_votes([spend(i, Tb, sD, pD) for i in range(3)])    # Tb sealed by a quorum
    spend(3, Ta, sD, pD)                                                        # Ta bound by one
    dp_b = {"kind": "seal", "sigil": xD, "gen": 0, "parcel": tgt(pxD), "seal": seal_y}
    for i in range(3):
        release(i, sD, dp_b)                                   # Tb is dead: x is consumed by Ty
    pH, sH = mk("hh")                                          # H: the regression's dual
    pxH, xH = mk("hx")
    TyH, TbH, TaH, TgH = hdr([(xH, 0)], "e2"), hdr([(sH, 0), (xH, 0)], "e3"), hdr([(sH, 0)], "e4"), hdr([(sH, 1)], "e5")
    seal_yH = model.seal_from_votes([spend(i, TyH, xH, pxH) for i in range(4)])
    seal_aH = model.seal_from_votes([spend(i, TaH, sH, pH) for i in range(3)])  # Ta sealed by a quorum
    spend(3, TbH, sH, pH)                                                       # Tb bound by one
    release(3, sH, {"kind": "seal", "sigil": xH, "gen": 0, "parcel": tgt(pxH), "seal": seal_yH})
    spend(0, TF, sF, pF)                                       # F: gen skipping (bound at gen 2)
    spend(3, TG, sG, pG)                                       # G: bound by o3 alone

    nxt = charter_body("rot", 1, [k.pk for k in new], charter_hash(body0))
    other = charter_body("rot", 1, [kp(813).pk], charter_hash(body0))
    sc.run("o0", "status", 1700000200, sD)
    sc.run("o0", "freeze", 1700000201, dict(nxt, prev="00" * 32))   # does not extend ours: not frozen
    sc.run("o0", "spend", 1700000202, req(hdr([(sF, 3)], "f2"), sF, pF))  # still active: bound at gen 2
    snap0 = sc.run("o0", "freeze", 1700000203, nxt)["ok"]["snapshot"]
    sc.run("o0", "freeze", 1700000204, nxt)                    # the same successor: signed again
    sc.run("o0", "freeze", 1700000205, other)                  # a different successor: refused
    sc.run("o0", "spend", 1700000206, req(TA, sA, pA))         # frozen: no more votes
    sc.run("o0", "release", 1700000207, sC, dpC)               # nor releases
    sc.run("o0", "status", 1700000208, sA)
    sigs, snaps = {old[0].pk: sign_charter(old[0], nxt)}, [snap0]
    for w in o[1:]:
        sig, snap = w.freeze(nxt)
        sigs[w.pk] = sig
        snaps.append(snap)
    reg1 = Registry()
    reg1.add_chain(X, chain0 + [{"body": nxt, "sigs": sigs}])

    # n1: a new key adopting every snapshot, plus junk a lying predecessor could send.
    authA = {"home": X, "lock": pA["lock"], "salt": pA["salt"], "header": TA, "unlock": 5}
    stranger = vote(kp(813), X, sA, 0, "7" * 64)
    junk = [5, "x", {"zz": "notalist", sA: [7, "e", {"kind": "bind", "auth": authA},
                                            {"kind": "bind", "auth": None},
                                            {"kind": "release", "tid": model.transition_id(TA), "header": TA, "proof": {}},
                                            {"kind": "vote", "vote": stranger},
                                            {"kind": "vote", "vote": vote(new[0], "other", sA, 0, "7" * 64)},
                                            {"kind": "vote"}, {"kind": "mystery"}]}]
    n1 = sc.add("n1", Witness(new[0], reg1, lambda: clock[0]), 810, "v1", adopt=True)
    sc.run("n1", "spend", 1700000300, req(TA, sA, pA))          # not adopted yet: inactive
    sc.run("n1", "adopt", 1700000301, X, 0, snaps)              # not a member of version 0
    sc.run("n1", "adopt", 1700000302, X, 1, snaps + junk)
    for s in (sA, sB, sC, xC, sD, xD, sF, sG, "unknown"):
        sc.run("n1", "record", 1700000303, s)
    sc.run("n1", "spend", 1700000310, req(TA, sA, pA))          # inherited binding: votes under v1
    sc.run("n1", "spend", 1700000311, req(TB1, sB, pB))         # contested: conflict
    sc.run("n1", "spend", 1700000312, req(hdr([(sB, 1)], "b3"), sB, pB))  # contested: release first
    sc.run("n1", "spend", 1700000313, req(Ta, sD, pD))          # regression 1: Ta is never sealed at (sD,0)
    sc.run("n1", "spend", 1700000314, req(Tg, sD, pD))          # contested at gen 1
    sc.run("n1", "release", 1700000315, sD, {"kind": "seal", "sigil": sD, "gen": 0, "parcel": tgt(pD),
                                              "seal": dict(seal_b, votes=seal_b["votes"][:2])})  # below quorum
    sc.run("n1", "release", 1700000316, sD, {"kind": "seal", "sigil": sD, "gen": 0, "parcel": tgt(pD), "seal": seal_b})
    sc.run("n1", "record", 1700000317, sD)
    sc.run("n1", "spend", 1700000318, req(Tg, sD, pD))          # recovered at gen 1
    sc.run("n1", "spend", 1700000319, req(Ta, sD, pD))          # still never Ta
    sc.run("n1", "release", 1700000320, sB, {"kind": "seal", "sigil": sB, "gen": 0, "parcel": tgt(pB), "seal": seal_b})
    sc.run("n1", "spend", 1700000321, req(TF, sF, pF))
    sc.run("n1", "spend", 1700000322, req(TC1, sC, pC))
    sc.run("n1", "status", 1700000323, sB)
    sc.run("n1", "record", 1700000324, sH)                     # regression 2: contested, Ta the candidate
    sc.run("n1", "spend", 1700000325, req(TgH, sH, pH))        # s is consumed by Ta: never Tg
    sc.run("n1", "release", 1700000326, sH, {"kind": "seal", "sigil": sH, "gen": 0, "parcel": tgt(pH), "seal": seal_aH})
    sc.run("n1", "spend", 1700000327, req(TgH, sH, pH))
    sc.run("n1", "spend", 1700000328, req(TaH, sH, pH))

    # r3: o3's key re-used in v1. It adopts o0..o2's snapshots and brings its own votes
    # (Network.rotate's re-used-key path), so it abstains where o3 already voted.
    own = [{s: [{"kind": "vote", "vote": v} for v in r.votes] for s, r in o[3].records.items()}]
    sc.add("r3", Witness(old[3], reg1, lambda: clock[0]), 803, "v1", adopt=True)
    sc.run("r3", "adopt", 1700000400, X, 1, snaps[:3] + own)
    for s in (sA, sB, sC, sD, sG, sH):
        sc.run("r3", "record", 1700000401, s)
    sc.run("r3", "spend", 1700000402, req(TgH, sH, pH))        # bound to Ta at gen 0 (abstaining there)
    sc.run("r3", "spend", 1700000403, req(TaH, sH, pH))
    sc.run("r3", "spend", 1700000410, req(TB1, sB, pB))         # abstains: o3 voted TB2 at (sB,0)
    sc.run("r3", "spend", 1700000411, req(TA, sA, pA))          # the same tid it voted: fine
    sc.run("r3", "spend", 1700000412, req(Tg, sD, pD))          # regression 2's dual: past its own vote
    sc.run("r3", "spend", 1700000413, req(TG, sG, pG))          # stale: it voted TG at gen 0
    sc.run("r3", "release", 1700000414, sB, {"kind": "seal", "sigil": sB, "gen": 0, "parcel": tgt(pB),
                                              "seal": model.seal_from_votes([o[i].status(sB)["votes"][0] for i in range(3)])})
    sc.run("r3", "record", 1700000415, sB)
    return sc.done(registries={"v0": {X: chain0}, "v1": {X: reg1.chain(X)}}, cid=X)


def stamp_key(bits: int = 1024):
    """A deterministic RSA key (seeded prime search), so the vectors never change."""
    r = random.Random(20261028)

    def probably_prime(n):
        if n < 2 or any(n % p == 0 for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)):
            return n in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
        d, s = n - 1, 0
        while d % 2 == 0:
            d, s = d // 2, s + 1
        for _ in range(40):
            x = pow(r.randrange(2, n - 1), d, n)
            if x in (1, n - 1):
                continue
            for _ in range(s - 1):
                x = pow(x, 2, n)
                if x == n - 1:
                    break
            else:
                return False
        return True

    def prime(b):
        while True:
            c = r.getrandbits(b) | (3 << (b - 2)) | 1
            if probably_prime(c):
                return c

    e = 65537
    while True:
        p, q = prime(bits // 2), prime(bits // 2)
        lam = math.lcm(p - 1, q - 1)
        if p != q and math.gcd(e, lam) == 1:
            return p * q, e, pow(e, -1, lam)


def stamp_cases():
    from sigil.stamps import StampMint, full_domain_hash, unblind, verify_stamp
    n, e, d = stamp_key()
    pub = {"n": n, "e": e}
    mint = StampMint.from_numbers(n, e, d)
    fdh = [{"serial": s, "fdh": format(full_domain_hash(n, s), "x")}
           for s in ("", "00", "0123456789abcdef0123456789abcdef", "é😀", "x" * 300)]
    blinds = []
    for i, serial in enumerate(["aa" * 16, "bb" * 16, "s"]):
        rr = (0x1234567 + 7919 * i) % n
        blinded = (full_domain_hash(n, serial) * pow(rr, e, n)) % n
        bsig = mint.sign_blinded(blinded)
        sig = unblind(pub, bsig, rr)
        blinds.append({"serial": serial, "r": format(rr, "x"), "blinded": format(blinded, "x"),
                       "blind_sig": format(bsig, "x"), "sig": format(sig, "x")})
    good = {"serial": blinds[0]["serial"], "sig": blinds[0]["sig"]}
    stamps = [
        ("valid", good), ("uppercase hex", dict(good, sig=good["sig"].upper())),
        ("other serial", dict(good, serial=blinds[1]["serial"])),
        ("sig = n", dict(good, sig=format(n, "x"))), ("sig = 0", dict(good, sig="0")),
        ("sig + n", dict(good, sig=format(int(good["sig"], 16) + n, "x"))),
        ("not hex", dict(good, sig="zz")), ("empty", dict(good, sig="")), ("missing sig", {"serial": good["serial"]}),
        ("sig not a string", dict(good, sig=5)),
        # Python's int(x, 16) also takes a 0x prefix and a sign; Rust takes plain hex only.
        ("0x prefix", dict(good, sig="0x" + good["sig"]), False),
        ("plus sign", dict(good, sig="+" + good["sig"]), False),
    ]
    verify_out = []
    for case in stamps:
        entry = {"name": case[0], "stamp": case[1], "python": verify_stamp(pub, case[1])}
        if len(case) > 2:
            entry["rust"] = case[2]
        verify_out.append(entry)

    # A stamp-selling witness: sell, redeem once, refuse spent, missing and forged stamps.
    _, X, chainX = constellation("stamped", 900, 4)
    reg = Registry()
    reg.add_chain(X, chainX)
    clock = [1700000000]
    sc = Script(clock)
    w = sc.add("s0", Witness(kp(900), reg, lambda: clock[0], stamp_mint=StampMint.from_numbers(n, e, d)), 900, "v0",
               stamps=True)
    w.join(X, 0)
    owner = kp(950)

    def req(salt, stamp=None, home=X):
        p = {"home": X, "lock": locks.sig(owner.pk), "salt": salt}
        s = model.sigil_of(p)
        h = {"inputs": [[s, 0]], "body": "ab" * 32}
        tid = model.transition_id(h)
        u = locks.empty_unlock(1700000600)
        u["sigs"][owner.pk] = locks.sign_unlock(owner, s, tid, 1700000600)
        r = {"sigil": s, "header": h, "home": home, "lock": p["lock"], "salt": salt, "unlock": u}
        if stamp is not None:
            r["stamp"] = stamp
        return r

    st = [{"serial": b["serial"], "sig": b["sig"]} for b in blinds]
    for b in blinds:
        sc.run("s0", "sell_stamp", 1700000001, b["blinded"])
    sc.run("s0", "sell_stamp", 1700000002, "0")                       # out of range
    sc.run("s0", "sell_stamp", 1700000002, format(n, "x"))            # out of range
    sc.run("s0", "sell_stamp", 1700000002, "zz")                      # not hex
    sc.run("s0", "spend", 1700000010, req("01"))                      # no stamp
    sc.run("s0", "spend", 1700000011, req("01", dict(st[0], sig="0")))  # forged stamp
    sc.run("s0", "spend", 1700000012, req("01", {"serial": 5, "sig": st[0]["sig"]}))
    sc.run("s0", "spend", 1700000013, req("01", "not a stamp"))
    sc.run("s0", "spend", 1700000014, req("01", st[0]))               # redeemed: votes
    sc.run("s0", "spend", 1700000015, req("01", st[0]))               # spent, even for the same request
    sc.run("s0", "spend", 1700000016, req("02", st[1], home="elsewhere"))  # refused, the stamp is used up
    sc.run("s0", "spend", 1700000017, req("02", st[1]))
    sc.run("s0", "spend", 1700000018, req("02", st[2]))
    sc.run("s0", "spend", 1700000019, "not a request")
    return {"key": {"n": format(n, "x"), "e": format(e, "x"), "d": format(d, "x")}, "fdh": fdh, "blind": blinds,
            "verify": verify_out, "script": sc.done(registries={"v0": {X: chainX}}, cid=X)}


def gossip_script():
    """Gossip admission on a witness: chains, forks, proofs, caps (sigil/gossip.py)."""
    from sigil import gossip as G
    from sigil.charter import charter_hash as ch
    keys = [kp(1000 + i) for i in range(4)]
    body0 = charter_body("gsp", 0, [k.pk for k in keys], None)
    X = constellation_id(body0)
    chain0 = [{"body": body0, "sigs": {}}]
    reg = Registry()
    reg.add_chain(X, chain0)
    clock = [1700000000]
    sc = Script(clock)
    w = sc.add("g0", Witness(keys[0], reg, lambda: clock[0]), 1000, "v0")
    w.join(X, 0)
    newk = [kp(1010 + i) for i in range(4)]

    def charter(version, prev_body, members, signers, name="gsp"):
        b = charter_body(name, version, [k.pk for k in members], ch(prev_body))
        return {"body": b, "sigs": {k.pk: sign_charter(k, b) for k in signers}}

    v1 = charter(1, body0, newk, keys[:3])
    v1b = dict(v1, sigs={k.pk: sign_charter(k, v1["body"]) for k in keys[1:]})  # same body, other signers
    fork = charter(1, body0, [kp(1020)], keys[1:])
    weak = charter(1, body0, [kp(1021)], keys[:2])                              # 2 of 4: not a quorum
    v2 = charter(2, v1["body"], newk, newk[:3])

    def eqv(k, cid, version, sigil="11" * 32):
        return {"a": vote(k, cid, sigil, 0, "aa" * 32, version=version), "b": vote(k, cid, sigil, 0, "bb" * 32, version=version)}

    zk = [kp(1030 + i) for i in range(4)]
    zb = charter_body("z", 0, [k.pk for k in zk], None)
    Z = constellation_id(zb)
    za = {"constellation": Z, "prefix": [{"body": zb, "sigs": {}}],
          "a": charter(1, zb, [kp(1040)], zk[:3], "z"), "b": charter(1, zb, [kp(1041)], zk[1:], "z")}
    g = charter_body("lone", 0, ["aa" * 32], None)

    run = lambda now, op, *a: sc.run("g0", op, now, *a)  # noqa: E731
    run(1700000001, "proofs")
    run(1700000002, "gossip", {"proofs": [eqv(newk[0], X, 1)]})        # v1 not known yet: dropped
    run(1700000003, "gossip", {"charters": {X: chain0 + [weak]}})        # not a quorum
    run(1700000004, "gossip", {"charters": {X: chain0 + [v1]}, "proofs": [eqv(newk[0], X, 1)]})  # learned, then the proof
    run(1700000005, "gossip", {"charters": {X: chain0 + [v1]}})
    run(1700000006, "gossip", {"charters": {X: chain0 + [v1b, v2]}})     # other sigs on v1: extends, no fork
    run(1700000007, "gossip", {"charters": {X: chain0 + [fork]}})        # a fork: kept as evidence
    run(1700000008, "gossip", {"charters": {X: [{"body": charter_body("gsp", 0, ["bb" * 32], None), "sigs": {}}]}})
    run(1700000009, "gossip", {"charters": {constellation_id(g): [{"body": g, "sigs": {}}]}})
    run(1700000010, "gossip", {"proofs": [eqv(keys[1], X, 0), eqv(keys[1], X, 0), eqv(keys[2], X, 0),
                                           {"a": eqv(keys[3], X, 0)["a"], "b": eqv(keys[3], X, 0)["a"]},
                                           dict(eqv(keys[3], X, 0), b=dict(eqv(keys[3], X, 0)["b"], sig="00" * 64)),
                                           eqv(kp(1099), X, 0), eqv(keys[3], X, 7), {"a": "x"}, 5, None,
                                           dict(eqv(keys[3], X, 0), extra=1)]})
    run(1700000011, "gossip", {"forks": [za, za, dict(za, b=za["a"]), dict(za, constellation=X), {"constellation": 5}, 7]})
    run(1700000012, "gossip", {"proofs": [eqv(keys[1], X, 0)] * (G.MAX_PROOFS + 1)})
    run(1700000013, "gossip", {"forks": [{}] * (G.MAX_FORKS + 1)})
    run(1700000014, "gossip", {"charters": {str(i): [] for i in range(G.MAX_CHARTERS + 1)}})
    run(1700000015, "gossip", {"charters": {X: [{}] * (G.MAX_CHAIN + 1)}})
    run(1700000016, "gossip", {"proofs": "x"})
    run(1700000017, "gossip", {"charters": []})
    run(1700000018, "gossip", {"charters": None})
    run(1700000019, "gossip", {"charters": {X: [5, {}]}, "proofs": [], "forks": []})
    run(1700000020, "gossip", {})
    run(1700000021, "proofs")
    run(1700000022, "charters")
    return sc.done(registries={"v0": {X: chain0}}, cid=X)


def main():
    vectors = {
        "canonical": canonical_cases(), "keys": key_cases(), "model": model_cases(), "locks": lock_cases(),
        "proofs": proof_cases(), "witness": witness_script(), "rotation": rotation_script(),
        "stamps": stamp_cases(), "gossip": gossip_script(),
    }
    json.dump(vectors, sys.stdout, sort_keys=True, indent=None, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
