"""Atomic multi-party transitions, e.g. a swap between two assets.

One transition consumes inputs from both parties and pays each the other's
asset. It is valid only when *every* input is sealed to it, so either both
legs happen or neither does — even when the inputs live in different
constellations that never communicate with each other.
"""

from . import model
from .wallet import Wallet


def _pays(body: dict, address: dict, asset: str, amount: int) -> bool:
    return any(
        o["home"] == address["home"] and o["lock"] == address["lock"] and o["salt"] == address["salt"]
        and o["asset"] == asset and o["amount"] == amount
        for o in body["outputs"]
    )


def propose_swap(a: Wallet, a_asset: str, a_amount: int, b: Wallet, b_asset: str, b_amount: int):
    """Build (but do not sign) a swap transition. Returns everything both sides need."""
    to_b, to_a = b.address(), a.address()
    a_refs, a_outs = a.payment_outputs(a_asset, a_amount, to_b)
    b_refs, b_outs = b.payment_outputs(b_asset, b_amount, to_a)
    # Each side must be able to verify the other's inputs.
    a.dossier.merge(b.dossier.ancestry({r["tx"] for r in b_refs}))
    b.dossier.merge(a.dossier.ancestry({r["tx"] for r in a_refs}))
    gens = {h["sigil"]: h["gen"] for h in b.holdings.values()}
    header, body, _ = a.prepare(a_refs + b_refs, a_outs + b_outs, memo="swap", gens=gens)
    terms = {"a": (to_a, b_asset, b_amount), "b": (to_b, a_asset, a_amount)}
    return header, body, terms


def atomic_swap(a: Wallet, a_asset: str, a_amount: int, b: Wallet, b_asset: str, b_amount: int) -> str:
    header, body, terms = propose_swap(a, a_asset, a_amount, b, b_asset, b_amount)
    tid = model.transition_id(header)
    # Each party checks it is paid before signing anything.
    for party, key in ((a, "a"), (b, "b")):
        if not _pays(body, *terms[key]):
            raise ValueError(f"{party.name}: swap does not pay the agreed amount")
    unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
    a.seal(header, body, unlocks)          # either party can coordinate sealing
    b.dossier.merge(a.dossier.ancestry({r["tx"] for r in body["inputs"]}))
    for seal in a.dossier.seals.values():
        if seal["tid"] == tid:
            b.dossier.add_seal(seal)
    for party in (a, b):
        party.finalise(header, body, unlocks)
        party.verifier.verify_transition(party.dossier, tid)
    return tid
