"""Wire objects: parcels, sigils, transitions, votes, seals.

All wire objects are plain dicts so that their hash is exactly the hash of
what goes over the wire. The functions here are the single source of truth
for how each object is shaped and identified (see docs/SPEC.md §3).
"""

from .encoding import digest

# Placeholders only legal inside a genesis transition: they resolve to the
# asset being created (whose id is the genesis transition id) and to its
# mint right.
SELF_ASSET = ""
SELF_MINT = "mint:"
MINT_PREFIX = "mint:"


# ---------------------------------------------------------------- parcels

def parcel(home: str, asset: str, amount: int, lock: dict, salt: str) -> dict:
    """A unit of value. ``home`` names the constellation that attests its sigil."""
    return {"home": home, "asset": asset, "amount": amount, "lock": lock, "salt": salt}


def sigil_of(p: dict) -> str:
    """The single-use identifier of a parcel.

    It commits to where the parcel lives and how it is unlocked, but not to
    the asset or amount, so witnesses learn nothing about value.
    """
    return digest("sigil", {"home": p["home"], "lock": p["lock"], "salt": p["salt"]})


def ref(tid: str, index: int) -> dict:
    return {"tx": tid, "i": index}


def parcel_id(r: dict) -> str:
    return digest("parcel", r)


def resolve_asset(asset: str, tid: str) -> str:
    if asset == SELF_ASSET:
        return tid
    if asset == SELF_MINT:
        return MINT_PREFIX + tid
    return asset


def base_asset(asset: str) -> str:
    return asset[len(MINT_PREFIX):] if asset.startswith(MINT_PREFIX) else asset


# ------------------------------------------------------------ transitions

def body(inputs: list, outputs: list, genesis: dict | None = None, memo: str = "") -> dict:
    return {"inputs": inputs, "outputs": outputs, "genesis": genesis, "memo": memo}


def body_hash(b: dict) -> str:
    return digest("body", b)


def header(input_sigils: list, b: dict) -> dict:
    """The only part of a transition a witness ever sees.

    ``input_sigils`` is a list of ``[sigil, generation]`` pairs; the body is
    represented only by its hash.
    """
    return {"inputs": [[s, g] for s, g in input_sigils], "body": body_hash(b)}


def transition_id(h: dict) -> str:
    return digest("transition", h)


def unlock_message(sigil: str, tid: str, expires) -> dict:
    """What a lock's signatures sign: 'consume <sigil> in <transition>, if bound by <expires>'.

    ``expires`` (a time) bounds when a witness may *newly* bind the sigil
    for this authorisation, so an owner whose spend failed knows when no
    delayed request can still bind it (SPEC §5.1).
    """
    return {"sigil": sigil, "tid": tid, "expires": expires}


# ------------------------------------------------------------ votes/seals

VOTE_FIELDS = ("constellation", "version", "witness", "sigil", "gen", "tid", "time")


def vote_payload(v: dict) -> dict:
    return {k: v[k] for k in VOTE_FIELDS}


def seal_from_votes(votes: list) -> dict:
    """Compress matching votes into a seal (a quorum certificate)."""
    first = votes[0]
    return {
        "constellation": first["constellation"],
        "version": first["version"],
        "sigil": first["sigil"],
        "gen": first["gen"],
        "tid": first["tid"],
        "votes": [{"witness": v["witness"], "time": v["time"], "sig": v["sig"]} for v in votes],
    }


def votes_of_seal(seal: dict) -> list:
    common = {k: seal[k] for k in ("constellation", "version", "sigil", "gen", "tid")}
    return [dict(common, **v) for v in seal["votes"]]


def seal_key(sigil: str, tid: str) -> str:
    return f"{sigil}:{tid}"
