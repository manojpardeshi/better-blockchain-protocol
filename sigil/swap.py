"""Atomic multi-party transitions, e.g. a swap between two assets.

One transition consumes inputs from both parties and pays each the other's
asset. It is valid only when *every* input is sealed to it, so either both
legs happen or neither does — even when the inputs live in different
constellations that never communicate with each other.

Each party also adds a *kill switch*: a one-unit parcel of its own that comes
back to it in the outputs, whose unlock it withholds until it has seen the
other party's inputs bound. A counter-party that binds our inputs and then
stalls cannot hold them hostage: we spend our kill switch elsewhere, which is
a death proof for the swap, and ``Wallet.abort`` frees our inputs.
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
    kills, kill_outs = [], []
    for w in (a, b):
        k = w.kill_switch()
        back = w.address(k["parcel"]["home"])
        kills.append(k["ref"])
        kill_outs.append(model.parcel(back["home"], k["parcel"]["asset"], 1, back["lock"], back["salt"]))
    # Each side must be able to verify the other's inputs.
    a.dossier.merge(b.dossier.ancestry({r["tx"] for r in b_refs + kills[1:]}))
    b.dossier.merge(a.dossier.ancestry({r["tx"] for r in a_refs + kills[:1]}))
    gens = {h["sigil"]: h["gen"] for h in b.holdings.values()}
    header, body, _ = a.prepare(a_refs + b_refs + kills, a_outs + b_outs + kill_outs, memo="swap", gens=gens)
    terms = {"a": (to_a, b_asset, b_amount), "b": (to_b, a_asset, a_amount)}
    return header, body, terms


def atomic_swap(a: Wallet, a_asset: str, a_amount: int, b: Wallet, b_asset: str, b_amount: int) -> str:
    header, body, terms = propose_swap(a, a_asset, a_amount, b, b_asset, b_amount)
    tid = model.transition_id(header)
    # Each party checks it is paid before signing anything.
    for party, key in ((a, "a"), (b, "b")):
        if not _pays(body, *terms[key]):
            raise ValueError(f"{party.name}: swap does not pay the agreed amount")
    # 1. Main inputs: each party signs everything but its kill switch.
    unlocks = {**a.authorise(header, body), **b.authorise(header, body)}
    kills = (a.kill_switches | b.kill_switches) & {s for s, _ in header["inputs"]}
    a.seal(header, body, unlocks, only={s for s, _ in header["inputs"]} - kills)
    # 2. Every main input is bound: now each party releases its kill switch.
    unlocks.update({**a.authorise(header, body, release_kill=True), **b.authorise(header, body, release_kill=True)})
    a.seal(header, body, unlocks, only=kills)  # either party can coordinate sealing
    b.dossier.merge(a.dossier.ancestry({r["tx"] for r in body["inputs"]}))
    for seal in a.dossier.seals.values():
        if seal["tid"] == tid:
            b.dossier.add_seal(seal)
    for party in (a, b):
        party.finalise(header, body, unlocks)
        party.verifier.verify_transition(party.dossier, tid)
    return tid
