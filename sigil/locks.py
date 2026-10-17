"""Locks: tiny, total predicates that decide *who* may consume a sigil.

A lock is a JSON tree. It is evaluated against an *unlock* (signatures,
preimages, equivocation proofs) for one specific ``(sigil, transition)``
pair, so an authorisation can never be replayed into another transition.
There are no loops, no state and no gas: evaluation is linear in the size
of the lock.
"""

from .crypto import KeyPair, verify
from .encoding import hash_preimage
from .model import unlock_message
from .proofs import verify_equivocation

MAX_DEPTH = 8
MAX_NODES = 64


def sig(pk: str) -> dict:
    return {"op": "sig", "pk": pk}


def multi(k: int, pks: list) -> dict:
    return {"op": "multi", "k": k, "pks": list(pks)}


def after(t: int) -> dict:
    return {"op": "after", "t": t}


def before(t: int) -> dict:
    return {"op": "before", "t": t}


def hashlock(h: str) -> dict:
    return {"op": "hash", "h": h}


def equivocation(witness_pk: str) -> dict:
    """Satisfied by anyone holding proof that ``witness_pk`` equivocated."""
    return {"op": "equivocation", "witness": witness_pk}


def all_of(*locks) -> dict:
    return {"op": "all", "of": list(locks)}


def any_of(*locks) -> dict:
    return {"op": "any", "of": list(locks)}


def never() -> dict:
    """Provably unspendable (burn)."""
    return {"op": "never"}


def empty_unlock() -> dict:
    return {"sigs": {}, "preimages": {}, "equivocations": []}


def merge_unlocks(*unlocks) -> dict:
    out = empty_unlock()
    for u in unlocks:
        out["sigs"].update(u.get("sigs", {}))
        out["preimages"].update(u.get("preimages", {}))
        out["equivocations"].extend(u.get("equivocations", []))
    return out


def sign_unlock(kp: KeyPair, sigil: str, tid: str) -> str:
    return kp.sign("unlock", unlock_message(sigil, tid))


def keys_in(lock: dict) -> set:
    """Every public key a lock could ask a signature from."""
    op = lock.get("op")
    if op == "sig":
        return {lock["pk"]}
    if op == "multi":
        return set(lock["pks"])
    if op in ("all", "any"):
        return set().union(*(keys_in(x) for x in lock["of"])) if lock["of"] else set()
    return set()


def well_formed(lock, depth: int = 0, budget: list | None = None) -> bool:
    budget = budget if budget is not None else [MAX_NODES]
    budget[0] -= 1
    if budget[0] < 0 or depth > MAX_DEPTH or not isinstance(lock, dict):
        return False
    op = lock.get("op")
    try:
        if op == "sig":
            return isinstance(lock["pk"], str) and len(lock) == 2
        if op == "multi":
            return (
                isinstance(lock["k"], int) and not isinstance(lock["k"], bool)
                and 1 <= lock["k"] <= len(lock["pks"]) and len(set(lock["pks"])) == len(lock["pks"])
                and all(isinstance(p, str) for p in lock["pks"]) and len(lock) == 3
            )
        if op in ("after", "before"):
            return isinstance(lock["t"], int) and not isinstance(lock["t"], bool) and len(lock) == 2
        if op == "hash":
            return isinstance(lock["h"], str) and len(lock) == 2
        if op == "equivocation":
            return isinstance(lock["witness"], str) and len(lock) == 2
        if op in ("all", "any"):
            return (
                isinstance(lock["of"], list) and lock["of"] and len(lock) == 2
                and all(well_formed(x, depth + 1, budget) for x in lock["of"])
            )
        if op == "never":
            return len(lock) == 1
    except (KeyError, TypeError):
        return False
    return False


def evaluate(lock: dict, unlock: dict, sigil: str, tid: str, now: int | None) -> bool:
    """Is ``lock`` satisfied for consuming ``sigil`` in ``tid``?

    ``now`` is the evaluator's clock. Holders re-checking a sealed
    transition pass ``None``: time conditions were already enforced by the
    witnesses that sealed it and are treated as satisfied.
    """
    if not well_formed(lock):
        return False
    msg = unlock_message(sigil, tid)
    sigs = unlock.get("sigs", {})

    def has_sig(pk):
        s = sigs.get(pk)
        return isinstance(s, str) and verify(pk, "unlock", msg, s)

    def ev(node):
        op = node["op"]
        if op == "sig":
            return has_sig(node["pk"])
        if op == "multi":
            return sum(1 for pk in node["pks"] if has_sig(pk)) >= node["k"]
        if op == "after":
            return now is None or now >= node["t"]
        if op == "before":
            return now is None or now < node["t"]
        if op == "hash":
            pre = unlock.get("preimages", {}).get(node["h"])
            try:
                return isinstance(pre, str) and hash_preimage(pre) == node["h"]
            except ValueError:
                return False
        if op == "equivocation":
            return any(
                p.get("a", {}).get("witness") == node["witness"] and verify_equivocation(p)
                for p in unlock.get("equivocations", [])
                if isinstance(p, dict)
            )
        if op == "all":
            return all(ev(x) for x in node["of"])
        if op == "any":
            return any(ev(x) for x in node["of"])
        return False  # "never"

    return ev(lock)
