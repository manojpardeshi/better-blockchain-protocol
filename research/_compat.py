"""Glue between the research scripts and the reference implementation.

The research code never edits ``sigil/``. This module only:

* puts the repository root on ``sys.path`` so ``import sigil`` works when a
  script is run directly (``python3 research/measure_dossiers.py``);
* bridges a known in-flight state of the reference wallet. Commit 4f52887
  ("owner-signed expiry on spend authorisations, format only") made
  ``locks.sign_unlock`` take an ``expires`` argument and made witnesses
  require an integer ``unlock["expires"]``, while ``Wallet.authorise`` is
  updated in a follow-up commit. Until that lands, ``Wallet.authorise``
  raises ``TypeError``. ``ensure_wallet_signs_expiry()`` detects exactly
  that state and installs a faithful copy of ``Wallet.authorise`` that
  signs ``expires = now + ttl``. Once the wallet is fixed upstream the
  detection fails and nothing is patched.
"""

import inspect
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from sigil import locks, model  # noqa: E402
from sigil import wallet as _wallet  # noqa: E402
from sigil.locks import keys_in  # noqa: E402

DEFAULT_TTL = 3600


def _needs_patch() -> bool:
    wants_expiry = "expires" in inspect.signature(locks.sign_unlock).parameters
    wallet_passes_it = "expires" in inspect.getsource(_wallet.Wallet.authorise)
    return wants_expiry and not wallet_passes_it


def ensure_wallet_signs_expiry(ttl: int = DEFAULT_TTL) -> bool:
    """Patch ``Wallet.authorise`` if (and only if) it predates signed expiry."""
    if not _needs_patch():
        return False

    def authorise(self, header: dict, body: dict, extra: dict | None = None) -> dict:
        # Same as sigil.wallet.Wallet.authorise, plus an owner-signed expiry.
        tid = model.transition_id(header)
        expires = int(self.network.clock()) + ttl
        unlocks = {}
        for r, (s, g) in zip(body["inputs"], header["inputs"]):
            h = self.holdings.get(model.parcel_id(r))
            if h is None:
                continue
            prior = self.pledged.get(s)
            if prior is not None and prior[0] == g and prior[1] != tid:
                raise ValueError("refusing to equivocate: sigil already pledged")
            u = locks.empty_unlock(expires)
            for pk in keys_in(h["parcel"]["lock"]) & set(self.keys):
                u["sigs"][pk] = locks.sign_unlock(self.keys[pk], s, tid, expires)
            unlocks[s] = locks.merge_unlocks(u, (extra or {}).get(s, {}))
            self.pledged[s] = (g, tid)
        return unlocks

    _wallet.Wallet.authorise = authorise
    return True


def sign_unlock(kp, sigil: str, tid: str, expires: int = 2**40) -> dict:
    """An unlock for a ``sig`` lock, in whichever unlock format the reference uses."""
    if "expires" in inspect.signature(locks.sign_unlock).parameters:
        u = locks.empty_unlock(expires)
        u["sigs"][kp.pk] = locks.sign_unlock(kp, sigil, tid, expires)
    else:  # pragma: no cover - pre-4f52887 format
        u = locks.empty_unlock()
        u["sigs"][kp.pk] = locks.sign_unlock(kp, sigil, tid)
    return u
