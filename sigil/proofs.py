"""Verification of votes, seals, equivocation proofs and death proofs.

These are the only cryptographic facts the protocol relies on:

* a *seal* proves a quorum of a constellation bound a sigil (at a
  generation) to exactly one transition;
* an *equivocation proof* proves a witness signed two different
  transitions for the same sigil and generation;
* a *death proof* proves a transition can never be sealed, because one of
  its inputs is provably bound elsewhere at the generation it requires.
"""

from .charter import Registry, quorum
from .crypto import verify
from .model import vote_payload, votes_of_seal


def verify_vote(v: dict) -> bool:
    try:
        return verify(v["witness"], "vote", vote_payload(v), v["sig"])
    except (KeyError, TypeError):
        return False


def _counted_witnesses(votes: list, registry: Registry, convicted=frozenset()) -> tuple[set, dict | None]:
    """Distinct, non-convicted charter members with valid signatures."""
    if not votes:
        return set(), None
    cid, version = votes[0]["constellation"], votes[0]["version"]
    charter = registry.charter(cid, version)
    if charter is None:
        return set(), None
    members = set(charter["witnesses"])
    counted = set()
    for v in votes:
        if v["constellation"] != cid or v["version"] != version:
            return set(), None
        pk = v["witness"]
        if pk in members and pk not in convicted and pk not in counted and verify_vote(v):
            counted.add(pk)
    return counted, charter


def verify_seal(seal: dict, registry: Registry, convicted=frozenset()) -> bool:
    try:
        counted, charter = _counted_witnesses(votes_of_seal(seal), registry, convicted)
    except (KeyError, TypeError):
        return False
    return charter is not None and len(counted) >= quorum(len(charter["witnesses"]))


def verify_equivocation(proof: dict) -> bool:
    """Two valid votes by one witness, same sigil and generation, different transitions."""
    try:
        a, b = proof["a"], proof["b"]
        same = all(a[k] == b[k] for k in ("witness", "constellation", "sigil", "gen"))
        return same and a["tid"] != b["tid"] and verify_vote(a) and verify_vote(b)
    except (KeyError, TypeError):
        return False


def proves_dead(header: dict, tid: str, proof: dict, registry: Registry) -> bool:
    """Does ``proof`` show that transition ``tid`` (with ``header``) can never be sealed?

    A transition names, for every input, the generation at which it must
    be sealed. If some input is sealed to a different transition at that
    generation (``kind == "seal"``), or a quorum of witnesses voted for
    other transitions at that generation (``kind == "votes"``), then quorum
    intersection guarantees ``tid`` never collects a seal for that input.
    """
    try:
        target, gen = proof["sigil"], proof["gen"]
        if [target, gen] not in header["inputs"]:
            return False
        if proof["kind"] == "seal":
            seal = proof["seal"]
            return (
                seal["sigil"] == target
                and seal["gen"] == gen
                and seal["tid"] != tid
                and verify_seal(seal, registry)
            )
        if proof["kind"] == "votes":
            votes = proof["votes"]
            if any(v["sigil"] != target or v["gen"] != gen or v["tid"] == tid for v in votes):
                return False
            counted, charter = _counted_witnesses(votes, registry)
            return charter is not None and len(counted) >= quorum(len(charter["witnesses"]))
    except (KeyError, TypeError):
        return False
    return False
