"""Invalid local testnet sizes must fail before writing launcher state."""

import contextlib
import io
import os
import tempfile
import unittest
from unittest.mock import patch

from testnet import up
from testnet.launcher import Testnet


class TestnetConfigTests(unittest.TestCase):
    def test_create_rejects_invalid_sizes_without_side_effects(self):
        for constellations, witnesses in ((0, 1), (-1, 1), (1, 0), (1, -1), (1, 129)):
            with self.subTest(constellations=constellations, witnesses=witnesses):
                with tempfile.TemporaryDirectory() as directory:
                    with patch("testnet.launcher._witnessd", side_effect=AssertionError("started keygen")):
                        with self.assertRaises(ValueError):
                            Testnet(directory).create(constellations, witnesses)
                    self.assertEqual(os.listdir(directory), [])

    def test_up_reports_invalid_size_as_usage_error(self):
        with tempfile.TemporaryDirectory() as directory:
            with contextlib.redirect_stderr(io.StringIO()) as stderr:
                with self.assertRaises(SystemExit) as raised:
                    up.main(["--dir", directory, "--constellations", "0"])
            self.assertEqual(raised.exception.code, 2)
            self.assertIn("constellations", stderr.getvalue())
            self.assertEqual(os.listdir(directory), [])


if __name__ == "__main__":
    unittest.main()
