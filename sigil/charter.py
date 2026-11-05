"""Constellation charters: who the witnesses are, and how that changes.

A constellation is identified by the hash of its first charter. Each later
charter version must be signed by a quorum of the previous version's
*authority*, so a holder can verify the whole membership history from the
id alone. The authority is the previous version's witnesses, or, if that
version names a successor committee (SPEC §5.5), the committee: a version
with a committee is succeeded, cooperatively or after a dead-man period, only
with the committee's signatures.
"""

from .crypto import KeyPair, verify
from .encoding import canonical, digest

# Size of one charter version (SPEC §3.7). Genesis charters need no signatures and
# anyone may gossip one, so without these one 1 MiB message could register a
# constellation of ~14,000 witnesses (or a 1 MiB name, or 1 MiB of junk signatures).
MAX_WITNESSES = 128            # members of one charter version
MAX_CHARTER_BYTES = 64 << 10   # enc(charter): its body and signatures


def faults(n: int) -> int:
    """Byzantine witnesses tolerated by a constellation of size n."""
    return (n - 1) // 3


def quorum(n: int) -> int:
    """Votes needed for a seal: any two quorums share an honest witness."""
    return n - faults(n)


def successor_clause(committee: list, dead_man: int) -> dict:
    """A charter's successor committee (SPEC §3.7, §5.5)."""
    succ = {"committee": list(committee), "dead_man": dead_man}
    if not valid_successor(succ):
        raise ValueError(f"a committee is a list of 1..{MAX_WITNESSES} distinct keys and dead_man a positive integer")
    return succ


def valid_successor(succ) -> bool:
    """A successor clause: exactly ``{committee, dead_man}``, 1..MAX_WITNESSES distinct
    string keys and a positive integer (booleans are not integers)."""
    try:
        c, d = succ["committee"], succ["dead_man"]
        return (isinstance(succ, dict) and set(succ) == {"committee", "dead_man"} and isinstance(c, list)
                and 0 < len(c) <= MAX_WITNESSES and all(isinstance(k, str) for k in c) and len(set(c)) == len(c)
                and isinstance(d, int) and not isinstance(d, bool) and d > 0)
    except (KeyError, TypeError):
        return False


def charter_body(name: str, version: int, witnesses: list, prev: str | None, successor: dict | None = None) -> dict:
    if len(set(witnesses)) != len(witnesses) or not witnesses:
        raise ValueError("witness list must be non-empty and unique")
    if len(witnesses) > MAX_WITNESSES:
        raise ValueError(f"a charter names at most {MAX_WITNESSES} witnesses")
    body = {"name": name, "version": version, "witnesses": list(witnesses), "prev": prev}
    if successor is not None:
        if not valid_successor(successor):
            raise ValueError("malformed successor clause")
        body["successor"] = {"committee": list(successor["committee"]), "dead_man": successor["dead_man"]}
    return body


def committee_of(body: dict) -> list | None:
    """The successor committee a charter body names, or None."""
    succ = body.get("successor")
    return list(succ["committee"]) if succ is not None else None


def authority(body: dict) -> list:
    """Whose quorum must sign the next version: the committee if there is one, else the witnesses."""
    c = committee_of(body)
    return c if c is not None else list(body["witnesses"])


def signers(body: dict, sigs: dict, keys) -> set:
    """Members of ``keys`` with a valid charter signature on ``body`` in ``sigs``."""
    keys = set(keys)
    return {pk for pk, sig in sigs.items() if pk in keys and verify(pk, "charter", body, sig)}


def taken_over(chain: list, version: int) -> bool:
    """Was ``version`` succeeded WITHOUT its members' cooperation (a dead-man takeover)?

    True when the version names a committee, a next version exists, and that next
    charter does not carry signatures of a quorum of the version's own witnesses
    (a cooperative rotation carries their FREEZE signatures, SPEC §5.5). Seals of
    such a version come from keys whose operators may be gone: holders SHOULD
    deep-confirm them (SPEC §9).
    """
    if not 0 <= version < len(chain) - 1:
        return False
    body, nxt = chain[version]["body"], chain[version + 1]
    if committee_of(body) is None:
        return False
    ws = body["witnesses"]
    return len(signers(nxt["body"], nxt.get("sigs", {}), ws)) < quorum(len(ws))


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
    for c in chain:
        ws = c["body"]["witnesses"]
        if not ws or len(set(ws)) != len(ws):  # an empty charter would accept unsigned evidence
            return False
        if len(ws) > MAX_WITNESSES or len(canonical(c)) > MAX_CHARTER_BYTES:
            return False
        if "successor" in c["body"] and not valid_successor(c["body"]["successor"]):
            return False
    for prev, cur in zip(chain, chain[1:]):
        pb, cb = prev["body"], cur["body"]
        if cb["version"] != pb["version"] + 1 or cb["prev"] != charter_hash(pb):
            return False
        # The authority of the previous version: its committee if it names one
        # (a rotation or a succession of it alike), else its witnesses.
        auth = set(authority(pb))
        if len(signers(cb, cur["sigs"], auth)) < quorum(len(auth)):
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

    def committee(self, cid: str, version: int) -> list | None:
        """The successor committee of a charter version, or None (SPEC §5.5)."""
        body = self.charter(cid, version)
        return committee_of(body) if body is not None else None

    def __contains__(self, cid: str) -> bool:
        return cid in self._chains

    def ids(self) -> list:
        return list(self._chains)
