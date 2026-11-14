"""The benchmark must not publish measurements from a disagreeing guest."""

import contextlib
import io
import json
import os
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from research.rv32_cycles import run


class GuestAgreementGate(unittest.TestCase):
    PROFILE = "PROFILE parse=1 encode=2 blake2b=3 ed25519=0 logic=4 hashes=1 signatures=0\nRETIRED 10\n"

    def run_with_guest(self, result):
        with tempfile.TemporaryDirectory() as tmp:
            output = os.path.join(tmp, "results.json")
            scenario = {"name": "case", "inputs": 0, "n": 4, "votes": 0,
                        "witness": {}, "expected": "a" * 64}
            with patch.object(run, "HERE", tmp), patch.object(run, "cargo_build"), \
                    patch.object(run, "scenarios", return_value=[scenario]), \
                    patch.object(run.subprocess, "run", return_value=result), \
                    contextlib.redirect_stdout(io.StringIO()):
                try:
                    rows = run.main(["--json", output])
                except RuntimeError as exc:
                    self.assertFalse(os.path.exists(output))
                    return str(exc), None
            with open(output) as f:
                saved = json.load(f)
            return rows, saved

    def test_matching_digest_writes_results(self):
        result = subprocess.CompletedProcess([], 0,
            "STATEMENT " + "a" * 64 + "\n" + self.PROFILE, "")
        rows, saved = self.run_with_guest(result)
        self.assertEqual(rows, saved)
        self.assertTrue(saved[0]["digest_matches_python"])

    def test_mismatched_digest_does_not_write_results(self):
        result = subprocess.CompletedProcess([], 0,
            "STATEMENT " + "b" * 64 + "\n" + self.PROFILE, "")
        message, saved = self.run_with_guest(result)
        self.assertIn("digest mismatch", message)
        self.assertIsNone(saved)

    def test_missing_digest_does_not_write_results(self):
        result = subprocess.CompletedProcess([], 0, self.PROFILE, "")
        message, saved = self.run_with_guest(result)
        self.assertIn("no STATEMENT", message)
        self.assertIsNone(saved)

    def test_failed_guest_does_not_write_results(self):
        result = subprocess.CompletedProcess([], 1, "", "guest error")
        message, saved = self.run_with_guest(result)
        self.assertIn("guest failed", message)
        self.assertIsNone(saved)


if __name__ == "__main__":
    unittest.main()
