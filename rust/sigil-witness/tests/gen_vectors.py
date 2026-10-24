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

from sigil import locks, model
from sigil.charter import Registry, charter_body, constellation_id
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


def main():
    vectors = {
        "canonical": canonical_cases(), "keys": key_cases(), "model": model_cases(), "locks": lock_cases(),
        "proofs": proof_cases(), "witness": witness_script(),
    }
    json.dump(vectors, sys.stdout, sort_keys=True, indent=None, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
