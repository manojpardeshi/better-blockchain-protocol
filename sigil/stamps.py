"""Stamps: blind, unlinkable prepaid tokens that pay witnesses for attention.

A witness sells stamps by blind-signing serial numbers (RSA-FDH blind
signatures). Each spend request carries one stamp. Because the witness
never saw the serial it signed, it cannot link a stamp to its buyer, so
paying a witness reveals nothing about what is being attested, and a
witness cannot price-discriminate or censor a particular user.
"""

import hashlib
import math
import secrets

from cryptography.hazmat.primitives.asymmetric import rsa


def full_domain_hash(n: int, serial: str) -> int:
    size = (n.bit_length() + 7) // 8 + 16
    out, counter = b"", 0
    while len(out) < size:
        out += hashlib.blake2b(f"sigil/v0/stamp/{counter}/{serial}".encode(), digest_size=64).digest()
        counter += 1
    return int.from_bytes(out[:size], "big") % n


class StampMint:
    """The witness side: blind-signs serials and redeems each exactly once."""

    def __init__(self, bits: int = 2048):
        key = rsa.generate_private_key(public_exponent=65537, key_size=bits)
        nums = key.private_numbers()
        self.n, self.e, self._d = nums.public_numbers.n, nums.public_numbers.e, nums.d
        self._redeemed: set[str] = set()

    @property
    def public(self) -> dict:
        return {"n": self.n, "e": self.e}

    def sign_blinded(self, blinded: int) -> int:
        if not 0 < blinded < self.n:
            raise ValueError("blinded value out of range")
        return pow(blinded, self._d, self.n)

    def redeem(self, stamp) -> bool:
        if not isinstance(stamp, dict) or not isinstance(stamp.get("serial"), str) or stamp["serial"] in self._redeemed:
            return False
        if not verify_stamp(self.public, stamp):
            return False
        self._redeemed.add(stamp["serial"])
        return True

    def mark_redeemed(self, serials) -> None:
        """Restore serials redeemed before a restart (see ``sigil.store``)."""
        self._redeemed.update(serials)


def blind(public: dict, serial: str) -> tuple[int, int]:
    n, e = public["n"], public["e"]
    while True:
        r = secrets.randbelow(n - 2) + 2
        if math.gcd(r, n) == 1:
            break
    return (full_domain_hash(n, serial) * pow(r, e, n)) % n, r


def unblind(public: dict, blind_sig: int, r: int) -> int:
    return (blind_sig * pow(r, -1, public["n"])) % public["n"]


def verify_stamp(public: dict, stamp: dict) -> bool:
    try:
        sig = int(stamp["sig"], 16)
        return 0 < sig < public["n"] and pow(sig, public["e"], public["n"]) == full_domain_hash(public["n"], stamp["serial"])
    except (KeyError, TypeError, ValueError):
        return False


def buy_stamp(public: dict, sign_blinded) -> dict:
    """Client-side helper: obtain one stamp the seller cannot link to us.

    ``sign_blinded`` is the seller's blind-signing endpoint (in practice
    called after paying for the stamp through any channel).
    """
    serial = secrets.token_hex(16)
    blinded, r = blind(public, serial)
    sig = unblind(public, sign_blinded(blinded), r)
    if not verify_stamp(public, {"serial": serial, "sig": format(sig, "x")}):
        raise ValueError("seller returned an invalid blind signature")
    return {"serial": serial, "sig": format(sig, "x")}
