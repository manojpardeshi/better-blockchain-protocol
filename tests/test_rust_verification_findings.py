"""Findings from verifying the Rust witness that also affect the Python reference.

See docs/VERIFY_RUST.md. Each test asserts the intended behaviour and is marked
``expectedFailure`` until the reference is fixed.
"""

import time
import unittest

from sigil import locks
from sigil.crypto import KeyPair
from sigil.locks import evaluate


class EquivocationLockCost(unittest.TestCase):
    """Bug 4: every ``equivocation`` node re-verifies every equivocation proof in the unlock.

    A lock of 63 such nodes and an unlock full of proofs whose cheap checks pass (same
    witness, constellation, sigil, gen; different tids) but whose signatures do not verify
    costs (#nodes x #proofs) signature checks, all inside the server's single dispatch lock.
    Anyone can choose such a lock for their own parcel. Evaluation cost should be linear in
    the number of proofs, independent of how many nodes refer to the same witness.
    """

    @unittest.expectedFailure
    def test_cost_does_not_scale_with_node_count(self):
        w = KeyPair.from_seed(b"bug4-witness")

        def vote(t):
            return {"constellation": "C", "version": 0, "witness": w.pk, "sigil": "s", "gen": 0, "tid": t,
                    "time": 1, "sig": "11" * 64}

        unlock = locks.empty_unlock(0)
        unlock["equivocations"] = [{"a": vote(f"t{i}"), "b": vote(f"u{i}")} for i in range(60)]

        def cost(n):
            lock = locks.any_of(*[locks.equivocation(w.pk)] * n)
            t = time.perf_counter()
            self.assertFalse(evaluate(lock, unlock, "s", "t", 0))
            return time.perf_counter() - t

        one = min(cost(1) for _ in range(3))
        many = min(cost(63) for _ in range(3))
        self.assertLess(many, 10 * one, f"63 nodes cost {many / one:.1f}x one node")


if __name__ == "__main__":
    unittest.main()
