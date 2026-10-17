"""Ed25519 keys and domain-separated signatures."""

import hashlib

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)

from .encoding import DOMAIN, canonical


def signing_message(tag: str, obj) -> bytes:
    return DOMAIN + b"sig/" + tag.encode() + b"\x00" + canonical(obj)


class KeyPair:
    """An Ed25519 key pair. ``pk`` is the hex-encoded raw public key."""

    __slots__ = ("_sk", "pk")

    def __init__(self, sk: Ed25519PrivateKey):
        self._sk = sk
        self.pk = sk.public_key().public_bytes(
            serialization.Encoding.Raw, serialization.PublicFormat.Raw
        ).hex()

    @classmethod
    def generate(cls) -> "KeyPair":
        return cls(Ed25519PrivateKey.generate())

    @classmethod
    def from_seed(cls, seed: bytes) -> "KeyPair":
        return cls(Ed25519PrivateKey.from_private_bytes(hashlib.blake2b(seed, digest_size=32).digest()))

    def sign(self, tag: str, obj) -> str:
        return self._sk.sign(signing_message(tag, obj)).hex()

    def __repr__(self):
        return f"KeyPair({self.pk[:12]}…)"


def verify(pk: str, tag: str, obj, sig: str) -> bool:
    try:
        Ed25519PublicKey.from_public_bytes(bytes.fromhex(pk)).verify(
            bytes.fromhex(sig), signing_message(tag, obj)
        )
        return True
    except (InvalidSignature, ValueError, TypeError):
        return False
