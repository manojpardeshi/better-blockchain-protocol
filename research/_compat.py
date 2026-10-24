"""Glue between the research scripts and the reference implementation.

The research code never edits ``sigil/``. This module only:

* puts the repository root on ``sys.path`` so ``import sigil`` works when a
  script is run directly (``python3 research/measure_dossiers.py``);
* offers ``sign_unlock`` for tests that build unlocks by hand.
"""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from sigil import locks  # noqa: E402


def sign_unlock(kp, sigil: str, tid: str, expires: int = 2**40) -> dict:
    """An unlock for a ``sig`` lock signed by ``kp``."""
    u = locks.empty_unlock(expires)
    u["sigs"][kp.pk] = locks.sign_unlock(kp, sigil, tid, expires)
    return u
