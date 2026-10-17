"""Sigil: a chainless value protocol.

No blocks, no chain, no global order, no global state, no miners, no
validators executing transactions, no gas, no mempool, no native token.

* Value lives in *parcels*; each parcel has a single-use *sigil*.
* *Witnesses* attest only that a sigil was consumed once, by whom it was
  authorised — never what moved. A quorum of votes is a *seal*.
* *Holders* validate everything else client-side, from a *dossier* they
  carry with the parcel.

See docs/WHITEPAPER.md for the rationale and docs/SPEC.md for the rules.
"""

from .charter import Registry, faults, quorum
from .crypto import KeyPair
from .network import Network, SimClock
from .validate import Dossier, InvalidDossier, TrustPolicy, Verifier
from .wallet import SealFailed, Wallet
from .witness import Conflict, Rejected, Witness

__all__ = [
    "Conflict", "Dossier", "InvalidDossier", "KeyPair", "Network", "Registry", "Rejected",
    "SealFailed", "SimClock", "TrustPolicy", "Verifier", "Wallet", "Witness", "faults", "quorum",
]

__version__ = "0.1.0"
