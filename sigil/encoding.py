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
