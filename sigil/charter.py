"""Constellation charters: who the witnesses are, and how that changes.

A constellation is identified by the hash of its first charter. Each later
charter version must be signed by a quorum of the previous version, so a
holder can verify the whole membership history from the id alone.
"""

from .crypto import KeyPair, verify
from .encoding import digest


def faults(n: int) -> int:
    """Byzantine witnesses tolerated by a constellation of size n."""
    return (n - 1) // 3


def quorum(n: int) -> int:
    """Votes needed for a seal: any two quorums share an honest witness."""
    return n - faults(n)


def charter_body(name: str, version: int, witnesses: list, prev: str | None) -> dict:
    if len(set(witnesses)) != len(witnesses) or not witnesses:
        raise ValueError("witness list must be non-empty and unique")
    return {"name": name, "version": version, "witnesses": list(witnesses), "prev": prev}


def charter_hash(body: dict) -> str:
    return digest("charter", body)


def constellation_id(genesis_body: dict) -> str:
    return digest("constellation", genesis_body)


def sign_charter(kp: KeyPair, body: dict) -> str:
    return kp.sign("charter", body)


def verify_chain(cid: str, chain: list) -> bool:
    """Check a list of ``{"body", "sigs"}`` charters, version 0 first."""
    if not chain:
        return False
    first = chain[0]["body"]
    if first["version"] != 0 or first["prev"] is not None or constellation_id(first) != cid:
        return False
    for prev, cur in zip(chain, chain[1:]):
        pb, cb = prev["body"], cur["body"]
        if cb["version"] != pb["version"] + 1 or cb["prev"] != charter_hash(pb):
            return False
        members = set(pb["witnesses"])
        signers = {pk for pk, sig in cur["sigs"].items() if pk in members and verify(pk, "charter", cb, sig)}
        if len(signers) < quorum(len(members)):
            return False
    return True


class Registry:
    """The charters a participant knows about, verified on entry."""

    def __init__(self):
        self._chains: dict[str, list] = {}

    def add_chain(self, cid: str, chain: list) -> None:
        known = self._chains.get(cid, [])
        if len(chain) <= len(known):
            return
        if not verify_chain(cid, chain):
            raise ValueError(f"invalid charter chain for {cid[:12]}")
        if known and chain[: len(known)] != known:
            raise ValueError(f"charter fork for {cid[:12]}")
        self._chains[cid] = list(chain)

    def chain(self, cid: str) -> list:
        return list(self._chains.get(cid, []))

    def charter(self, cid: str, version: int) -> dict | None:
        chain = self._chains.get(cid)
        if chain is None or not 0 <= version < len(chain):
            return None
        return chain[version]["body"]

    def latest(self, cid: str) -> dict | None:
        chain = self._chains.get(cid)
        return chain[-1]["body"] if chain else None

    def __contains__(self, cid: str) -> bool:
        return cid in self._chains

    def ids(self) -> list:
        return list(self._chains)
