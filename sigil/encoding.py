"""Canonical encoding and domain-separated hashing.

Every object that is hashed or signed in Sigil is a JSON-native value
(dict / list / str / int / bool / None). Byte strings are carried as
lowercase hex. The canonical form is JSON with sorted keys and no
whitespace, so two implementations always agree on the bytes.
"""

import hashlib
import json

DOMAIN = b"sigil/v0/"


def canonical(obj) -> bytes:
    """Deterministic byte encoding of a JSON-native object."""
    return json.dumps(
        obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False
    ).encode()


def digest(tag: str, obj) -> str:
    """BLAKE2b-256 of ``obj`` under a domain tag, as hex.

    Domain separation guarantees that, e.g., a sigil id can never collide
    with a transition id even if the underlying objects are identical.
    """
    h = hashlib.blake2b(digest_size=32)
    h.update(DOMAIN + tag.encode() + b"\x00")
    h.update(canonical(obj))
    return h.hexdigest()


def hash_preimage(preimage_hex: str) -> str:
    """Hash used by hash-locks: BLAKE2b-256 of the raw preimage bytes."""
    return hashlib.blake2b(bytes.fromhex(preimage_hex), digest_size=32).hexdigest()


# The JSON both witness implementations can represent (docs/WIRE.md "Portable JSON"):
# integers in [-2**127, 2**127), finite floats, strings without lone UTF-16 surrogates,
# and at most ``MAX_DEPTH`` levels of nesting under a request body (the operator calls:
# ``ADMIN_DEPTH``). The Rust witness's parser refuses anything else, so the reference
# refuses it too: a witness of either kind then never binds, releases or stores what a
# witness of the other kind could not read back from a handover.
INT_MIN, INT_MAX = -(1 << 127), (1 << 127) - 1
MAX_DEPTH = 256
ADMIN_DEPTH = MAX_DEPTH + 16


def _portable_str(s: str) -> bool:
    try:
        s.encode("utf-8")
        return True
    except UnicodeEncodeError:  # a lone surrogate
        return False


def portable(x, max_depth: int = MAX_DEPTH, depth: int = 0) -> bool:
    """Is ``x`` portable JSON whose deepest value sits at most ``max_depth`` levels below ``x``
    (counted from ``depth``)? Iterative, so any nesting Python's parser produced is checked."""
    stack = [(x, depth)]
    while stack:
        v, d = stack.pop()
        if d > max_depth:
            return False
        if v is None or isinstance(v, bool):
            continue
        if isinstance(v, int):
            if not INT_MIN <= v <= INT_MAX:
                return False
        elif isinstance(v, float):
            if v != v or v in (float("inf"), float("-inf")):
                return False
        elif isinstance(v, str):
            if not _portable_str(v):
                return False
        elif isinstance(v, list):
            stack.extend((y, d + 1) for y in v)
        elif isinstance(v, dict):
            for k, y in v.items():
                if not isinstance(k, str) or not _portable_str(k):
                    return False
                stack.append((y, d + 1))
        else:
            return False
    return True
