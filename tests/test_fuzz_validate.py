"""Fuzzing the holder-side validator with malicious dossiers.

Contract under test: for ANY input, ``Verifier.verify_parcel`` either
returns a parcel or raises ``InvalidDossier`` (never another exception,
never hangs), and anything it accepts has a conserving, owner-authorised
history. The lock and proof checkers must return bools on any garbage.

Stdlib only. Seeds are fixed; scale with ``SIGIL_FUZZ_ITERS`` (default
keeps the whole file well under 20s).
"""

import copy
import os
import random
import unittest
from collections import Counter

from sigil import InvalidDossier, Network, Wallet
from sigil import locks, model
from sigil.charter import Registry
from sigil.locks import evaluate, well_formed
from sigil.model import MINT_PREFIX, base_asset
from sigil.proofs import proves_dead, verify_equivocation, verify_seal
from sigil.swap import atomic_swap
from sigil.validate import Dossier, TrustPolicy, Verifier

ITERS = int(os.environ.get("SIGIL_FUZZ_ITERS", "4000"))

HEX64 = "ab" * 32


# ------------------------------------------------------------ fixtures

def _build_world():
    net = Network()
    X = net.create_constellation("orion")
    Y = net.create_constellation("lyra")
    alice, bob, carol = Wallet("alice", net, X), Wallet("bob", net, Y), Wallet("carol", net, X)
    usd = alice.issue("USD", 1_000)
    gold = bob.issue("GOLD", 50, mint_cap=10)
    cases = []
    t1 = alice.pay(bob, usd, 300)
    cases.append((alice.dossier.ancestry([t1]), model.ref(t1, 0)))
    t2 = bob.pay(carol, usd, 120)
    cases.append((bob.dossier.ancestry([t2]), model.ref(t2, 0)))
    t3 = atomic_swap(alice, usd, 100, bob, gold, 5)
    cases.append((alice.dossier.ancestry([t3]), model.ref(t3, 0)))
    cases.append((alice.dossier.ancestry([t3]), model.ref(t3, 1)))
    t4 = bob.mint(gold, 3)
    cases.append((bob.dossier.ancestry([t4]), model.ref(t4, 0)))
    return net, cases


_WORLD = None


def world():
    global _WORLD
    if _WORLD is None:
        _WORLD = _build_world()
    return _WORLD


def fresh_verifier() -> Verifier:
    return Verifier(TrustPolicy(Registry()))


def to_raw(d: Dossier) -> dict:
    return copy.deepcopy({"transitions": d.transitions, "seals": d.seals, "charters": d.charters})


def from_raw(raw) -> Dossier:
    d = Dossier()
    if isinstance(raw, dict):
        d.transitions = raw.get("transitions")
        d.seals = raw.get("seals")
        d.charters = raw.get("charters")
    else:
        d.transitions = d.seals = d.charters = raw
    return d


# ------------------------------------------------------------ garbage

def garbage(rng: random.Random, depth: int = 0):
    k = rng.randrange(14 if depth < 3 else 9)
    if k == 0:
        return None
    if k == 1:
        return rng.choice([True, False])
    if k == 2:
        return rng.choice([0, -1, 1, 2, 10**80, -(10**80), 2**63])
    if k == 3:
        return rng.choice(["", "x", HEX64, "mint:", "mint:" + HEX64, "zz", "00"])
    if k == 4:
        return rng.choice([1.5, float("inf")])
    if k == 5:
        return rng.choice(["sig", "multi", "all", "any", "never", "hash", "after", "equivocation"])
    if k == 6:
        return rng.randrange(-3, 5)
    if k == 7:
        return rng.choice([[], {}, [HEX64, 0], {"op": "never"}])
    if k == 8:
        return HEX64[: rng.randrange(65)]
    if k in (9, 10):
        return [garbage(rng, depth + 1) for _ in range(rng.randrange(4))]
    if k == 11:
        return deep_nest(rng.randrange(1, 3000))
    keys = ["op", "pk", "pks", "k", "of", "t", "h", "witness", "a", "b", "sigs", "preimages",
            "equivocations", "votes", "sigil", "gen", "tid", "constellation", "version", "kind", "seal",
            "inputs", "outputs", "genesis", "body", "header", "unlocks", "tx", "i", "x"]
    return {rng.choice(keys): garbage(rng, depth + 1) for _ in range(rng.randrange(5))}


def deep_nest(n: int):
    x = {"op": "never"}
    for i in range(n):
        x = {"op": "all", "of": [x]} if i % 2 else [x]
    return x


def random_lock(rng: random.Random, depth: int = 0):
    ops = ["sig", "multi", "after", "before", "hash", "equivocation", "never", "all", "any"]
    op = rng.choice(ops if depth < 12 else ops[:7])
    if op == "sig":
        lk = {"op": "sig", "pk": rng.choice([HEX64, garbage(rng)])}
    elif op == "multi":
        pks = [rng.choice([HEX64, "cd" * 32, garbage(rng)]) for _ in range(rng.randrange(4))]
        lk = {"op": "multi", "k": rng.choice([0, 1, 2, len(pks), True, garbage(rng)]), "pks": pks}
    elif op in ("after", "before"):
        lk = {"op": op, "t": rng.choice([0, 10**30, -5, True, garbage(rng)])}
    elif op == "hash":
        lk = {"op": "hash", "h": rng.choice([HEX64, garbage(rng)])}
    elif op == "equivocation":
        lk = {"op": "equivocation", "witness": rng.choice([HEX64, garbage(rng)])}
    elif op == "never":
        lk = {"op": "never"}
    else:
        lk = {"op": op, "of": [random_lock(rng, depth + 1) for _ in range(rng.randrange(4))]}
    if rng.random() < 0.15:
        lk[rng.choice(["extra", "op", "of", "k"])] = garbage(rng)
    return lk


def random_unlock(rng: random.Random):
    if rng.random() < 0.3:
        return garbage(rng)
    u = {
        "sigs": rng.choice([{HEX64: "00" * 64}, {HEX64: garbage(rng)}, garbage(rng), {}]),
        "preimages": rng.choice([{HEX64: "00"}, {HEX64: "zz"}, {HEX64: garbage(rng)}, garbage(rng)]),
        "equivocations": rng.choice([[garbage(rng)], [{"a": garbage(rng), "b": garbage(rng)}],
                                     garbage(rng), [{"a": {"witness": HEX64}}]]),
    }
    if rng.random() < 0.3:
        del u[rng.choice(list(u))]
    return u


# ------------------------------------------------------------ mutation

def _containers(obj, path=()):
    """Every (path, container) pair inside ``obj``."""
    out = [(path, obj)]
    if len(path) > 40:  # don't descend into deliberately deep garbage
        return out
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, (dict, list)):
                out.extend(_containers(v, path + (k,)))
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            if isinstance(v, (dict, list)):
                out.extend(_containers(v, path + (i,)))
    return out


def _retype(rng, v):
    choices = [None, True, False, 0, -1, 10**100, "", str(v)[:64], [v], {"x": v}, [], {}]
    if isinstance(v, bool):
        choices.append(int(v))
    elif isinstance(v, int):
        choices += [-v, v + 1, v * 10**30, str(v), 0]
    elif isinstance(v, str):
        choices += [v[::-1], v + "00", v[:-1], int(len(v))]
    elif isinstance(v, list):
        choices += [v + v, v[::-1], v[1:]]
    elif isinstance(v, dict):
        choices += [list(v.values()), list(v)]
    return rng.choice(choices)


def mutate_generic(rng, raw):
    path, c = rng.choice(_containers(raw))
    if isinstance(c, dict):
        if not c or rng.random() < 0.1:
            c[rng.choice(["x", "op", "tx", "i", "inputs", "genesis"])] = garbage(rng)
            return
        k = rng.choice(list(c))
        op = rng.randrange(5)
        if op == 0:
            del c[k]
        elif op == 1:
            c[k] = _retype(rng, c[k])
        elif op == 2:
            c[k] = garbage(rng)
        elif op == 3 and len(c) > 1:
            k2 = rng.choice(list(c))
            c[k], c[k2] = c[k2], c[k]
        else:
            v = c.pop(k)
            c[rng.choice([str(k) + "x", str(k)[1:], "", "0"])] = v
    else:
        if not c:
            c.append(garbage(rng))
            return
        i = rng.randrange(len(c))
        op = rng.randrange(5)
        if op == 0:
            del c[i]
        elif op == 1:
            c[i] = _retype(rng, c[i])
        elif op == 2:
            c.append(copy.copy(c[i]))  # duplicate entry
        elif op == 3:
            c.insert(i, garbage(rng))
        else:
            j = rng.randrange(len(c))
            c[i], c[j] = c[j], c[i]


def mutate_semantic(rng, raw, others):
    """Targeted, structure-preserving attacks."""
    T, S = raw["transitions"], raw["seals"]
    tids = list(T)
    tid = rng.choice(tids)
    tx = T[tid]
    op = rng.randrange(12)
    if op == 0:  # inflate an output
        o = rng.choice(tx["body"]["outputs"])
        o["amount"] = rng.choice([o["amount"] + 1, 10**60, -o["amount"], 0])
    elif op == 1:  # duplicate an input in body and header
        if tx["body"]["inputs"]:
            tx["body"]["inputs"].append(tx["body"]["inputs"][0])
            tx["header"]["inputs"].append(tx["header"]["inputs"][0])
    elif op == 2 and len(S) >= 2:  # swap two seals
        a, b = rng.sample(list(S), 2)
        S[a], S[b] = S[b], S[a]
    elif op == 3:  # seal from another dossier/transition
        other = rng.choice(others)["seals"]
        if S and other:
            S[rng.choice(list(S))] = copy.deepcopy(rng.choice(list(other.values())))
    elif op == 4:  # drop unlocks
        tx["unlocks"] = rng.choice([{}, None, [], garbage(rng)])
    elif op == 5:  # bogus charters
        cid = rng.choice(list(raw["charters"]) or ["x"])
        raw["charters"][cid] = rng.choice([[], garbage(rng), [{"body": garbage(rng), "sigs": garbage(rng)}],
                                           raw["charters"].get(cid, []) * 2])
    elif op == 6:  # replace a lock with a random (possibly deep) one
        rng.choice(tx["body"]["outputs"])["lock"] = random_lock(rng)
    elif op == 7:  # random unlock
        if isinstance(tx["unlocks"], dict) and tx["unlocks"]:
            tx["unlocks"][rng.choice(list(tx["unlocks"]))] = random_unlock(rng)
    elif op == 8:  # re-point an input ref at another transition
        if tx["body"]["inputs"]:
            tx["body"]["inputs"][0] = {"tx": rng.choice(tids + [tid, "nope"]), "i": rng.choice([0, 1, -1, 99])}
    elif op == 9:  # turn a spend into a genesis
        tx["body"]["genesis"] = rng.choice([{"name": "X", "supply": 10**70}, {}, garbage(rng)])
    elif op == 10:  # seal fields
        if S:
            seal = S[rng.choice(list(S))]
            k = rng.choice(list(seal))
            seal[k] = _retype(rng, seal[k])
    else:  # remove a transition
        del T[rng.choice(tids)]


def cycle_dossier() -> dict:
    """Two hand-crafted transitions whose inputs point at each other."""
    def tx(prev):
        b = model.body([model.ref(prev, 0)], [model.parcel("c", "a", 1, locks.never(), "s")])
        return {"header": model.header([["s", 0]], b), "body": b, "unlocks": {}}
    return {"transitions": {"A": tx("B"), "B": tx("A"), "C": tx("C")}, "seals": {}, "charters": {}}


# ------------------------------------------------------------ oracle

def independent_conservation_ok(d: Dossier, tids) -> bool:
    for tid in tids:
        b = d.transitions[tid]["body"]
        if b["genesis"] is not None:
            continue
        tin, tout = Counter(), Counter()
        for r in b["inputs"]:
            p = d.output(r)
            tin[p["asset"]] += p["amount"]
        for o in b["outputs"]:
            if not (isinstance(o["amount"], int) and o["amount"] > 0):
                return False
            tout[o["asset"]] += o["amount"]
        for a in set(tin) | set(tout):
            x = base_asset(a)
            m = MINT_PREFIX + x
            if tin[x] + tin[m] != tout[x] + tout[m] or tout[m] > tin[m]:
                return False
    return True


class FuzzValidator(unittest.TestCase):
    def check(self, raw, ref, original: Dossier, orig_ref):
        v = fresh_verifier()
        d = from_raw(raw)
        try:
            p = v.verify_parcel(d, ref)
        except InvalidDossier:
            return False
        except Exception as e:  # pragma: no cover - this is the bug report
            self.fail(f"leaked {type(e).__name__}: {e!r}")
        # Accepted: the mutation must have been semantically irrelevant.
        # The (possibly mutated) ref must name a real output of the original.
        self.assertIsInstance(ref["i"], int)
        self.assertNotIsInstance(ref["i"], bool)
        self.assertEqual(p, original.output(ref))
        for tid in v._ok:
            self.assertEqual(model.transition_id(d.transitions[tid]["header"]), tid)
            self.assertIn(tid, original.transitions)
            self.assertEqual(d.transitions[tid]["body"], original.transitions[tid]["body"])
        self.assertTrue(independent_conservation_ok(d, v._ok))
        return True

    def test_originals_verify(self):
        _, cases = world()
        for d, r in cases:
            self.assertTrue(self.check(to_raw(d), r, d, r))

    def test_random_mutations(self):
        _, cases = world()
        raws = [to_raw(d) for d, _ in cases]
        rng = random.Random(0xC0FFEE)
        rejected = 0
        for it in range(ITERS):
            ci = rng.randrange(len(cases))
            d, r = cases[ci]
            raw = copy.deepcopy(raws[ci])
            ref = copy.deepcopy(r)
            for _ in range(rng.randrange(1, 4)):
                k = rng.random()
                try:
                    if k < 0.5:
                        mutate_generic(rng, raw)
                    elif k < 0.95:
                        mutate_semantic(rng, raw, raws)
                    elif k < 0.98:
                        ref = rng.choice([garbage(rng), {"tx": r["tx"], "i": garbage(rng)}, {"tx": garbage(rng), "i": 0}])
                    else:
                        raw = rng.choice([garbage(rng), {"transitions": garbage(rng), "seals": {}, "charters": {}}])
                except (KeyError, TypeError, IndexError, AttributeError, ValueError, RecursionError):
                    pass  # an earlier mutation broke the structure this one targets
            with self.subTest(it=it):
                if not self.check(raw, ref, d, r):
                    rejected += 1
        self.assertGreater(rejected, ITERS // 2)

    def test_cycles_terminate(self):
        raw = cycle_dossier()
        for tid in ("A", "B", "C"):
            with self.assertRaises(InvalidDossier):
                fresh_verifier().verify_parcel(from_raw(copy.deepcopy(raw)), model.ref(tid, 0))

    def test_verify_transition_garbage_tids(self):
        _, cases = world()
        d = cases[0][0]
        for tid in (None, 5, [], {}, ["x"], HEX64, ""):
            with self.assertRaises(InvalidDossier):
                fresh_verifier().verify_transition(d, tid)


class FuzzPredicates(unittest.TestCase):
    def test_locks_never_raise(self):
        rng = random.Random(1234)
        for it in range(ITERS * 2):
            lk = random_lock(rng) if rng.random() < 0.7 else garbage(rng)
            u = random_unlock(rng)
            s = rng.choice([HEX64, garbage(rng)])
            t = rng.choice([HEX64, garbage(rng)])
            now = rng.choice([None, 0, 10**40])
            with self.subTest(it=it):
                self.assertIsInstance(well_formed(lk), bool)
                self.assertIsInstance(evaluate(lk, u, s, t, now), bool)

    def test_proofs_never_raise(self):
        net, cases = world()
        seals = [s for d, _ in cases for s in d.seals.values()]
        rng = random.Random(4321)
        for it in range(ITERS):
            seal = copy.deepcopy(rng.choice(seals))
            if rng.random() < 0.8:
                mutate_generic(rng, seal)
            else:
                seal = garbage(rng)
            votes = model.votes_of_seal(rng.choice(seals))
            a, b = copy.deepcopy(rng.choice(votes)), copy.deepcopy(rng.choice(votes))
            proof = {"a": a, "b": b}
            if rng.random() < 0.8:
                mutate_generic(rng, proof)
            else:
                proof = garbage(rng)
            dead = {"kind": rng.choice(["seal", "votes", garbage(rng)]), "sigil": rng.choice([HEX64, garbage(rng)]),
                    "gen": rng.choice([0, garbage(rng)]), "seal": seal, "votes": rng.choice([votes, garbage(rng)])}
            if rng.random() < 0.5:
                mutate_generic(rng, dead)
            header = rng.choice([{"inputs": [[HEX64, 0]], "body": HEX64}, garbage(rng)])
            convicted = rng.choice([frozenset(), {HEX64}])
            with self.subTest(it=it):
                self.assertIsInstance(verify_seal(seal, net.registry, convicted), bool)
                self.assertIsInstance(verify_equivocation(proof), bool)
                self.assertIsInstance(proves_dead(header, rng.choice([HEX64, garbage(rng)]), dead, net.registry), bool)
                self.assertIsInstance(proves_dead(header, HEX64, garbage(rng), net.registry), bool)


class Regressions(unittest.TestCase):
    """One targeted test per crash the fuzzer found."""

    def setUp(self):
        _, cases = world()
        self.d, self.r = cases[0]
        self.tid = self.r["tx"]

    def reject(self, raw, ref=None):
        with self.assertRaises(InvalidDossier):
            fresh_verifier().verify_parcel(from_raw(raw), self.r if ref is None else ref)

    def test_cyclic_history_does_not_hang(self):
        # Used to loop forever: pending ancestors were re-pushed endlessly.
        self.reject(cycle_dossier(), model.ref("A", 0))
        self.reject(cycle_dossier(), model.ref("C", 0))

    def test_non_dict_charters(self):
        raw = to_raw(self.d)
        raw["charters"] = None  # AttributeError: .items()
        self.reject(raw)

    def test_bad_charter_chain_entries(self):
        raw = to_raw(self.d)
        cid = next(iter(raw["charters"]))
        raw["charters"][cid] = [{"body": None, "sigs": {}}]  # TypeError in verify_chain
        self.reject(raw)

    def test_non_dict_transitions(self):
        raw = to_raw(self.d)
        raw["transitions"] = []  # AttributeError: .get()
        self.reject(raw)
        raw = to_raw(self.d)
        raw["transitions"][self.tid] = "junk"
        self.reject(raw)

    def test_non_string_tids(self):
        for tid in (None, 5, ["x"], {}):  # TypeError slicing / hashing
            with self.assertRaises(InvalidDossier):
                fresh_verifier().verify_transition(self.d, tid)
        self.reject(to_raw(self.d), {"tx": ["x"], "i": 0})
        self.reject(to_raw(self.d), "not a ref")

    def test_non_dict_unlocks(self):
        raw = to_raw(self.d)
        raw["transitions"][self.tid]["unlocks"] = []  # AttributeError: .get()
        self.reject(raw)

    def test_deeply_nested_body(self):
        raw = to_raw(self.d)
        raw["transitions"][self.tid]["body"]["memo"] = deep_nest(50_000)  # RecursionError hashing
        self.reject(raw)

    def test_bool_output_index(self):
        self.reject(to_raw(self.d), {"tx": self.tid, "i": True})

    def test_evaluate_malformed_unlocks(self):
        lk = locks.any_of(locks.sig(HEX64), locks.hashlock(HEX64), locks.equivocation(HEX64))
        for u in ([], "x", None, 5, {"sigs": []}, {"preimages": "x"}, {"equivocations": 3},
                  {"equivocations": [{"a": "x"}]}, {"equivocations": [{"a": None, "b": {}}]}):
            self.assertIs(evaluate(lk, u, HEX64, HEX64, None), False)

    def test_well_formed_empty_combinator_is_bool(self):
        self.assertIs(well_formed({"op": "all", "of": []}), False)
        self.assertIs(well_formed({"op": "any", "of": []}), False)


if __name__ == "__main__":
    unittest.main()
