#!/usr/bin/env python3
"""Randomized differential test: the Python reference Witness vs the Rust witness.

    cargo build --release --manifest-path rust/sigil-witness/proofs/Cargo.toml --bin diff_driver
    PYTHONPATH=. python3 rust/sigil-witness/proofs/diff/differential.py [--episodes N] [--seed S]
    PYTHONPATH=. python3 rust/sigil-witness/proofs/diff/differential.py --canonical [--corpus DIR ...]

Witness mode: the same random request sequence (SPEND / RELEASE / STATUS, well-formed and
mutated) goes to an in-process `sigil.witness.Witness` and to the Rust witness (through the
JSON-lines driver `diff_driver`, which runs the real `sigil_witness::Witness`). Every request
is serialised once with `json.dumps` and both sides parse that same text, as on the wire.
Replies are compared byte for byte (votes are deterministic: Ed25519, fixed clock). After every
agreed step the STATUS of every sigil in the world is compared too. On the first divergence in
an episode the episode ends (states would differ from then on) and the divergence is classified:

* ``SAFETY``: Rust voted or released where Python did not, or both voted differently;
* ``STRICTER``: Rust refused (rejected / bad_request) where Python voted, released or conflicted;
* ``STRICTER-SEAL-ENTRY``: Rust refused a seal whose vote entries carry extra keys, which
  the reference ignores (a deliberate difference, see proofs.rs);
* ``STRICTER-NONSTR-SIGIL`` / ``MESSAGE-NONSTR-SIGIL``: a header input names a non-string
  sigil, which the reference tolerates and Rust refuses (deliberate);
* ``MESSAGE``: both refused, with a different kind or message;
* ``STRICTER-PARSE``: the Rust JSON parser refused the whole body (integers beyond i128, lone
  surrogates, ...), which the Rust server answers with 400;
* ``PANIC``: the Rust driver caught a panic.

Canonical mode: random JSON texts (and, with --corpus, every file of fuzz corpora) are parsed
and canonically encoded by both implementations and compared.

Exit status 1 if any SAFETY or PANIC divergence was seen.
"""

import argparse
import collections
import json
import math
import os
import random
import struct
import subprocess
import sys

from sigil import locks, model
from sigil.charter import Registry, charter_body, constellation_id
from sigil.crypto import KeyPair
from sigil.encoding import canonical, hash_preimage
from sigil.witness import Conflict, Rejected, Witness

HERE = os.path.dirname(os.path.abspath(__file__))
DRIVER = os.path.join(HERE, "..", "target", "release", "diff_driver")


def kp(tag, i):
    return KeyPair.from_seed(f"diff-{tag}-{i}".encode())


class Rust:
    def __init__(self):
        self.p = subprocess.Popen([DRIVER], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)

    def call(self, msg_text):
        self.p.stdin.write(msg_text + "\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        if not line:
            raise RuntimeError("diff_driver died")
        return json.loads(line)

    def close(self):
        self.p.stdin.close()
        self.p.wait()


def constellation(tag, n):
    keys = [kp(tag, i) for i in range(n)]
    body = charter_body(tag, 0, [k.pk for k in keys], None) if n else {"name": tag, "version": 0, "witnesses": [], "prev": None}
    cid = constellation_id(body)
    return keys, cid, [{"body": body, "sigs": {}}]


class World:
    def __init__(self, rng, empty_charter):
        self.rng = rng
        self.X, self.cX, chX = constellation("X", 4)
        self.Y, self.cY, chY = constellation("Y", 4)
        self.E, self.cE, chE = constellation("E", 1)
        self.chains = {self.cX: chX, self.cY: chY, self.cE: chE}
        if empty_charter:
            _, self.cZ, chZ = constellation("Z", 0)
            self.chains[self.cZ] = chZ
        self.homes = [self.cX] * 8 + [self.cY, self.cE] + ([self.cZ] if empty_charter else [])
        self.keys_of = {self.cX: self.X, self.cY: self.Y, self.cE: self.E}
        if empty_charter:
            self.keys_of[self.cZ] = []
        self.owners = [kp("O", i) for i in range(3)]
        self.bond = kp("B", 0)
        self.pre = "c0ffee"
        T = 1_700_000_100
        o = self.owners
        self.lock_menu = [
            ("sig", locks.sig(o[0].pk), [o[0]]),
            ("multi", locks.multi(2, [o[0].pk, o[1].pk, o[2].pk]), [o[0], o[2]]),
            ("after", locks.all_of(locks.sig(o[0].pk), locks.after(T)), [o[0]]),
            ("before", locks.any_of(locks.sig(o[1].pk), locks.before(T)), []),
            ("hash", locks.hashlock(hash_preimage(self.pre)), []),
            ("equiv", locks.equivocation(self.bond.pk), []),
            ("never", locks.never(), [o[0]]),
        ]
        self.parcels = []
        for i in range(14):
            home = self.homes[i % len(self.homes)]
            name, lock, signers = self.lock_menu[i % len(self.lock_menu)]
            p = {"home": home, "lock": lock, "salt": f"{i:02x}" * 16}
            self.parcels.append((p, model.sigil_of(p), name, signers))
        self.bodies = [model.body_hash(model.body([], [], memo=f"m{i}")) for i in range(4)]

    def registry(self):
        reg = Registry()
        for cid, ch in self.chains.items():
            reg.add_chain(cid, ch)
        return reg

    def sigils(self):
        return [s for _, s, _, _ in self.parcels]


def rand_value(rng, depth=0):
    c = rng.randrange(10)
    if c == 0:
        return None
    if c == 1:
        return rng.choice([True, False])
    if c == 2:
        if rng.random() < 0.05:
            return rng.choice([2**127, -(2**127) - 1, 10**40])  # beyond i128: Rust refuses the body
        return rng.choice([0, 1, -1, 2**62, 2**62 - 1, 2**63, 2**127 - 1, -(2**127)])
    if c == 3:
        return rng.choice([0.0, -0.0, 1.0, 1.5, 1e16, 5e-324, 1e-7, 123456789.125])
    if c == 4:
        return rng.choice(["", "x", "é", "\U0001f600", " ", "\x00", "\\u", "!contested", "a" * 64])
    if c == 5 and depth < 3:
        return [rand_value(rng, depth + 1) for _ in range(rng.randrange(3))]
    if c == 6 and depth < 3:
        return {rng.choice(["a", "op", "gen", "tid", "é", ""]): rand_value(rng, depth + 1) for _ in range(rng.randrange(3))}
    return rng.randrange(-3, 5)


def mutate(rng, obj, tags):
    """Apply one random structural mutation somewhere inside obj (a dict/list tree)."""
    path = []
    cur = obj
    while isinstance(cur, (dict, list)) and cur and rng.random() < 0.7:
        if isinstance(cur, dict):
            k = rng.choice(sorted(cur.keys()))
        else:
            k = rng.randrange(len(cur))
        path.append((cur, k))
        cur = cur[k]
    if not path:
        if isinstance(obj, dict):
            obj[rng.choice(["x", "op", "gen"])] = rand_value(rng)
            tags.append("add-top-key")
        return
    parent, k = path[-1]
    r = rng.randrange(5)
    if r == 0 and isinstance(parent, dict):
        del parent[k]
        tags.append(f"del:{k}")
    elif r == 1 and isinstance(parent, list):
        parent.insert(k, parent[k])
        tags.append("dup-elem")
    elif r == 2 and isinstance(parent, dict):
        parent[rng.choice(["x", "extra", "tid", "gen", "constellation", "op"])] = rand_value(rng)
        tags.append("add-key")
    else:
        parent[k] = rand_value(rng)
        tags.append(f"set:{k if isinstance(k, str) else 'idx'}")


class Episode:
    def __init__(self, world, rng, rust, steps):
        self.w, self.rng, self.rust, self.steps = world, rng, rust, steps
        self.reg = world.registry()
        self.now = 1_700_000_000
        self.py = Witness(world.X[0], self.reg, lambda: self.now)
        self.py.join(world.cX, 0)
        init = {"op": "init", "registry": world.chains, "cid": world.cX, "py_seed": "diff-X-0".encode().hex()}
        assert self.rust.call(json.dumps(init)) == {"ok": True}
        self.extra_votes = []  # votes signed by the harness (other keys), reused in proofs

    # ------------------------------------------------------------- generators

    def vote(self, k, cid, s, g, t):
        v = {"constellation": cid, "version": 0, "witness": k.pk, "sigil": s, "gen": g, "tid": t, "time": self.now}
        v["sig"] = k.sign("vote", model.vote_payload(v))
        return v

    def spend_req(self, tags):
        rng, w = self.rng, self.w
        local = [x for x in w.parcels if x[0]["home"] == w.cX]
        p, s, name, signers = rng.choice(local if rng.random() < 0.85 else w.parcels)
        rec = self.py.records.get(s)
        g = rng.choice([0, 0, 0, 1, 1, 2, 3])
        if rec is not None and rng.random() < 0.5:
            g = rec.gen + rng.choice([0, 0, 1])
        inputs = [[s, g]]
        for _ in range(rng.choice([0, 0, 1, 2])):
            _, s2, _, _ = rng.choice(w.parcels)
            if all(s2 != x[0] for x in inputs):
                inputs.append([s2, rng.choice([0, 1])])
        rng.shuffle(inputs)
        h = {"inputs": inputs, "body": rng.choice(w.bodies)}
        tid = model.transition_id(h)
        expires = self.now + rng.choice([600, 600, 30, 0, -1, -100])
        u = locks.empty_unlock(expires)
        who = list(signers)
        if rng.random() < 0.2:
            who = [rng.choice(w.owners)]
            tags.append("other-signer")
        for k in who:
            msg_exp = expires if rng.random() > 0.05 else expires + 1
            u["sigs"][k.pk] = locks.sign_unlock(k, s, tid, msg_exp)
        if name == "hash" and rng.random() < 0.8:
            u["preimages"][hash_preimage(w.pre)] = w.pre if rng.random() < 0.9 else "00"
        if name == "equiv" and rng.random() < 0.8:
            a = self.vote(w.bond, "Q", "q", 0, "t1")
            b = self.vote(w.bond, "Q", "q", 0, "t2" if rng.random() < 0.8 else "t1")
            u["equivocations"].append({"a": a, "b": b})
        req = {"sigil": s, "header": h, "home": p["home"], "lock": p["lock"], "salt": p["salt"], "unlock": u}
        req = json.loads(json.dumps(req))  # mutations must not reach the world's shared objects
        if rng.random() < 0.15:
            for _ in range(rng.randrange(1, 3)):
                mutate(rng, req, tags)
        if rng.random() < 0.01:
            req = rand_value(rng)
            tags.append("non-dict")
        return req

    def release_args(self, tags):
        rng, w = self.rng, self.w
        bound = [x for x in w.parcels if (r0 := self.py.records.get(x[1])) is not None and r0.tid is not None]
        p, s, _, _ = rng.choice(bound if bound and rng.random() < 0.85 else w.parcels)
        rec = self.py.records.get(s)
        if rec is None or rec.header is None:
            header = {"inputs": [[s, 0]], "body": w.bodies[0]}
            tid = model.transition_id(header)
        else:
            header, tid = rec.header, rec.tid
        ts, tg = rng.choice(header["inputs"])
        tp = next((pp for pp, ss, _, _ in w.parcels if ss == ts), p)
        src = tp["home"] if rng.random() < 0.8 else rng.choice(list(w.keys_of))
        keys = w.keys_of[src]
        held = [k for k in keys if k.pk != w.X[0].pk] or [kp("outsider", 0)]  # empty charter: a non-member signs
        n = rng.choice([len(held), len(held), max(0, len(held) - 1)])
        u = rng.choice(["e" * 64, "d" * 64, tid if rng.random() < 0.1 else "f" * 64])
        votes = [self.vote(k, src, ts, tg, u) for k in held[:n]]
        if rng.random() < 0.3:
            # Deep copy: the in-process status() hands out the witness's own vote dicts.
            votes += [json.loads(json.dumps(v)) for v in self.py.status(ts)["votes"] if v["gen"] == tg]
            tags.append("with-w0-votes")
        kind = rng.choice(["seal", "votes"])
        proof = {"kind": kind, "sigil": ts, "gen": tg, "parcel": {"home": tp["home"], "lock": tp["lock"], "salt": tp["salt"]}}
        if kind == "seal":
            proof["seal"] = model.seal_from_votes(votes) if votes else {
                "constellation": src, "version": 0, "sigil": ts, "gen": tg, "tid": u, "votes": []}
            if rng.random() < 0.1 and proof["seal"]["votes"]:
                proof["seal"]["votes"][0]["note"] = 1
                tags.append("seal-entry-extra-key")
        else:
            proof["votes"] = votes
        proof = json.loads(json.dumps(proof))  # the header/lock objects are shared with the world and the witness
        if rng.random() < 0.25:
            for _ in range(rng.randrange(1, 3)):
                mutate(rng, proof, tags)
        sigil = s if rng.random() > 0.03 else rand_value(rng)
        return [sigil, proof]

    # ------------------------------------------------------------------ steps

    def py_call(self, op, args):
        try:
            if op == "spend":
                return {"ok": self.py.spend(*args)}
            if op == "release":
                return {"ok": self.py.release(*args)}
            return {"ok": self.py.status(*args)}
        except Conflict as e:
            return {"error": "conflict", "vote": e.vote}
        except Rejected as e:
            return {"error": "rejected", "message": str(e)}
        except (ValueError, KeyError, TypeError, AttributeError):
            return {"error": "bad_request"}
        except Exception as e:  # noqa: BLE001
            return {"error": "internal", "message": type(e).__name__}

    def run(self, stats, examples):
        rng = self.rng
        for _ in range(self.steps):
            self.now += rng.choice([0, 1, 5, 30, 200])
            tags = []
            r = rng.random()
            if r < 0.6:
                op, args = "spend", [self.spend_req(tags)]
            elif r < 0.9:
                op, args = "release", self.release_args(tags)
            else:
                op, args = "status", [rng.choice(self.w.sigils() + [5, None, [1], "x"])]
            try:
                wire = json.dumps({"op": op, "now": self.now, "args": args})
            except (ValueError, TypeError):
                continue
            msg = json.loads(wire)
            py = self.py_call(op, msg["args"])
            ru = self.rust.call(wire)
            stats["steps"] += 1
            stats[f"{op}:{py.get('error', 'ok')}:{py.get('message', '')[:32]}"] += 1
            cls = classify(op, py, ru)
            if cls == "STRICTER" and op == "release" and seal_entries_have_extra_keys(msg["args"]):
                cls = "STRICTER-SEAL-ENTRY"  # deliberate: Rust refuses seal entries with extra keys
            if cls in ("STRICTER", "MESSAGE") and op == "spend" and non_string_header_sigil(msg["args"]):
                cls += "-NONSTR-SIGIL"  # deliberate: Rust requires every header sigil to be a string
            if cls == "SAFETY" and op == "release" and getattr(self.w, "cZ", None) and self.w.cZ in wire:
                cls = "SAFETY-EMPTY-CHARTER"  # bug 2: evidence from a constellation with no witnesses
            if cls:
                stats[cls] += 1
                key = (cls, op, py.get("error", "ok") + "/" + py.get("message", "")[:40], ru.get("error", "ok") + "/" + ru.get("message", "")[:40])
                if len(examples[key]) < 3:
                    examples[key].append({"tags": tags, "wire": wire[:3000], "py": json.dumps(py)[:400], "rust": json.dumps(ru)[:400]})
                return
            # Agreed: compare the whole state too.
            for s in self.w.sigils():
                pst = canonical(self.py.status(s)).decode()
                rst = self.rust.call(json.dumps({"op": "status", "now": self.now, "args": [s]}))
                if json.dumps(rst.get("ok"), sort_keys=True, separators=(",", ":")) != pst:
                    stats["STATE"] += 1
                    examples[("STATE", op, "", "")].append(
                        {"tags": tags, "wire": wire[:3000], "py": py, "rust": ru, "py_status": pst[:600], "rust_status": json.dumps(rst)[:600]})
                    return


def seal_entries_have_extra_keys(args):
    proof = args[1] if len(args) > 1 else None
    seal = proof.get("seal") if isinstance(proof, dict) else None
    votes = seal.get("votes") if isinstance(seal, dict) else None
    return isinstance(votes, list) and any(isinstance(e, dict) and set(e) - {"witness", "time", "sig"} for e in votes)


def non_string_header_sigil(args):
    req = args[0] if args else None
    h = req.get("header") if isinstance(req, dict) else None
    inputs = h.get("inputs") if isinstance(h, dict) else None
    return isinstance(inputs, list) and any(isinstance(x, list) and len(x) == 2 and not isinstance(x[0], str) for x in inputs)


def same(a, b):
    return json.dumps(a, sort_keys=True, separators=(",", ":")) == json.dumps(b, sort_keys=True, separators=(",", ":"))


def norm(r):
    return {"error": "bad_request"} if r.get("error") == "bad_request" else r


def classify(op, py, ru):
    parse_refusal = ru.get("error") == "bad_request" and ru.get("message", "").startswith("parse:")
    py, ru = norm(py), norm(ru)
    if same(py, ru):
        return None
    if parse_refusal:
        return "STRICTER-PARSE"  # the Rust parser refuses the whole body (e.g. an integer beyond i128)
    pe, re_ = py.get("error"), ru.get("error")
    if re_ == "panic":
        return "PANIC"
    if re_ is None and (pe is not None or not same(py["ok"], ru["ok"])):
        return "SAFETY" if op != "status" else "MESSAGE"
    if re_ == "conflict" and pe != "conflict":
        return "SAFETY" if op == "spend" else "MESSAGE"
    if re_ in ("rejected", "bad_request") and pe in (None, "conflict"):
        return "STRICTER"
    if pe == "conflict" and re_ == "conflict":
        return "SAFETY"  # different votes carried
    return "MESSAGE"


# ------------------------------------------------------------------------ canonical mode

def random_text(rng):
    kind = rng.randrange(8)
    if kind == 0:
        bits = rng.getrandbits(64)
        x = struct.unpack("<d", struct.pack("<Q", bits))[0]
        return repr(x) if math.isfinite(x) else "1.5"
    if kind == 1:
        return f"{rng.choice(['', '-'])}{rng.randint(0, 10**rng.randint(1, 25))}{rng.choice(['', '.0', '.5', 'e5', 'E-3', 'e+400', 'e-400'])}"
    if kind == 2:
        return str(rng.randint(-2**130, 2**130))
    if kind == 3:
        alphabet = [chr(c) for c in list(range(0x20, 0x7f)) + [0xe9, 0x2028, 0xfeff, 0x10000, 0x1f600]]
        s = "".join(rng.choice(alphabet) for _ in range(rng.randint(0, 10)))
        return json.dumps(s, ensure_ascii=bool(rng.getrandbits(1)))
    if kind == 4:
        esc = rng.choice(["\\ud83d\\ude00", "\\ud800", "\\udc00", "\\u0000", "\\u00e9", "\\/", "\\b\\f\\n\\r\\t", "\\ud83dx", "\\uD83D\\uDE00"])
        return f'"a{esc}b"'
    if kind == 5:
        return json.dumps(rand_value(rng), ensure_ascii=bool(rng.getrandbits(1)))
    if kind == 6:
        return rng.choice(["NaN", "Infinity", "-Infinity", " [1 , 2] ", "{\"a\":1,\"a\":2}", "[" * 300 + "]" * 300, "1.", ".5", "01", "-", "﻿1", "[1,]"])
    return json.dumps({rng.choice(["b", "a", "é", "~", "\U0001f600"]): rand_value(rng) for _ in range(rng.randrange(4))}, ensure_ascii=bool(rng.getrandbits(1)))


def py_canonical(text):
    try:
        return canonical(json.loads(text)).decode()
    except (ValueError, RecursionError, TypeError):
        return None


def canonical_mode(args, rust):
    rng = random.Random(args.seed)
    texts = [random_text(rng) for _ in range(args.texts)]
    for d in args.corpus or []:
        for name in sorted(os.listdir(d)):
            raw = open(os.path.join(d, name), "rb").read()
            try:
                texts.append(raw.decode("utf-8"))
            except UnicodeDecodeError:
                pass
    stats = collections.Counter()
    examples = collections.defaultdict(list)
    for t in texts:
        if any(0xD800 <= ord(c) <= 0xDFFF for c in t):
            continue
        py = py_canonical(t)
        ru = rust.call(json.dumps({"op": "canonical", "args": [t]}))
        if ru.get("error") == "panic":
            k = "PANIC"
        elif py is not None and "ok" in ru:
            k = "agree" if py == ru["ok"] else "DIFFERENT-ENCODING"
        elif py is None and "ok" in ru:
            k = "RUST-ACCEPTS-PYTHON-REJECTS"
        elif py is not None:
            k = "rust-stricter"
        else:
            k = "both-reject"
        stats[k] += 1
        if k not in ("agree", "both-reject") and len(examples[k]) < 8:
            examples[k].append({"text": t[:200], "py": py and py[:200], "rust": ru})
    print(json.dumps({"texts": len(texts), "stats": stats}, indent=1))
    for k, v in examples.items():
        print(f"--- {k}")
        for e in v:
            print("   ", json.dumps(e, ensure_ascii=True)[:500])
    return stats["PANIC"] + stats["DIFFERENT-ENCODING"] + stats["RUST-ACCEPTS-PYTHON-REJECTS"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--episodes", type=int, default=500)
    ap.add_argument("--steps", type=int, default=40)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--empty-charter", action="store_true", help="also register a constellation with no witnesses (bug 2)")
    ap.add_argument("--canonical", action="store_true")
    ap.add_argument("--texts", type=int, default=20000)
    ap.add_argument("--corpus", action="append")
    args = ap.parse_args()
    rust = Rust()
    if args.canonical:
        bad = canonical_mode(args, rust)
        rust.close()
        sys.exit(1 if bad else 0)
    rng = random.Random(args.seed)
    world = World(rng, args.empty_charter)
    stats = collections.Counter()
    examples = collections.defaultdict(list)
    for _ in range(args.episodes):
        Episode(world, rng, rust, args.steps).run(stats, examples)
    rust.close()
    print(json.dumps({"episodes": args.episodes, "stats": stats}, indent=1, sort_keys=True))
    for key in sorted(examples, key=lambda k: (k[0] != "SAFETY", k)):
        print(f"--- {key[0]} {key[1]}: python {key[2]!r} vs rust {key[3]!r}  ({len(examples[key])} examples kept)")
        for e in examples[key][:2]:
            print("    tags:", e["tags"])
            if key[0] not in ("STRICTER-PARSE", "STRICTER-SEAL-ENTRY"):
                print("    wire:", e["wire"])
                print("    py_status:", e.get("py_status"))
                print("    rust_status:", e.get("rust_status"))
            print("    py:  ", e.get("py"))
            print("    rust:", e.get("rust"))
    sys.exit(1 if stats["SAFETY"] or stats["PANIC"] else 0)


if __name__ == "__main__":
    main()
