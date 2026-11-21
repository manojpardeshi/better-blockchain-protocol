"""A lost or substituted stamp key must not silently invalidate sold stamps."""

import json
import os
import shutil
import sqlite3
import unittest

from sigil.server import RemoteWitness
from sigil.stamps import buy_stamp, verify_stamp
from sigil.witnessd import load_mint
from sigil.store import WitnessStore

from tests.integration.compat_harness import (Daemon, make_tmpdir, new_constellation,
                                              requires_rust, run_cli)


def _read_with_v2_format_guard(path: str) -> None:
    """The previous Python reader's format check, applied to actual on-disk rows."""
    with sqlite3.connect(path) as db:
        for kind, value in db.execute("SELECT kind, value FROM log ORDER BY seq"):
            if kind == "format":
                v = json.loads(value)
                if not (isinstance(v, int) and not isinstance(v, bool) and v <= 2):
                    raise ValueError(f"store format {v!r} is newer than this version reads")


class StampKeyRestartTests(unittest.TestCase):
    def exercise(self, kind: str) -> None:
        d = make_tmpdir(self, f"stamp-key-{kind}")
        c = new_constellation(d, kind, 1)
        store = os.path.join(d, f"witness.{kind}")
        daemon = Daemon(kind, c["keys"][0], c["registry"], c["cid"], store,
                        os.path.join(d, "witness.log"), args=["--stamps"])
        self.addCleanup(daemon.stop)
        daemon.start()
        witness = RemoteWitness(daemon.url)
        public = witness.stamps.public
        sold = buy_stamp(public, witness.sell_stamp)
        self.assertTrue(verify_stamp(public, sold))
        daemon.stop()
        if kind == "python":
            # A v2 reader's format guard must refuse a store that pins a stamp key.
            with sqlite3.connect(store) as db:
                version = json.loads(db.execute("SELECT value FROM log WHERE kind = 'format' ORDER BY seq DESC LIMIT 1")
                                     .fetchone()[0])
            self.assertEqual(version, 3)
            with self.assertRaisesRegex(ValueError, "newer than this version reads"):
                _read_with_v2_format_guard(store)

        # The key survives a normal restart, so a previously sold stamp still verifies.
        daemon.start()
        self.assertEqual(RemoteWitness(daemon.url).stamps.public, public)
        daemon.stop()

        sidecar = store + ".stamps.json"
        backup = sidecar + ".saved"
        os.rename(sidecar, backup)
        try:
            failed = run_cli(daemon.command())
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("missing stamp key", failed.stdout + failed.stderr)
            self.assertFalse(os.path.exists(sidecar), "startup recreated a lost stamp key")
            # An explicit first-activation flag cannot override an already pinned key.
            failed = run_cli(daemon.command() + ["--init-stamps"])
            self.assertNotEqual(failed.returncode, 0)
            self.assertFalse(os.path.exists(sidecar))
        finally:
            os.rename(backup, sidecar)

        # A different sidecar is also refused, even if its file is well formed.
        other = os.path.join(d, "other.stamps.json")
        load_mint(other, bits=1024)
        shutil.copyfile(sidecar, backup)
        try:
            shutil.copyfile(other, sidecar)
            failed = run_cli(daemon.command())
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("differs from the key pinned", failed.stdout + failed.stderr)
        finally:
            os.replace(backup, sidecar)

        # A public-key match alone is insufficient if the private exponent is damaged.
        shutil.copyfile(sidecar, backup)
        try:
            with open(sidecar) as f:
                numbers = json.load(f)
            numbers["d"] = "1"
            with open(sidecar, "w") as f:
                json.dump(numbers, f)
            failed = run_cli(daemon.command())
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("private exponent does not match", failed.stdout + failed.stderr)
        finally:
            os.replace(backup, sidecar)

        daemon.start()
        self.assertEqual(RemoteWitness(daemon.url).stamps.public, public)
        self.assertTrue(verify_stamp(RemoteWitness(daemon.url).stamps.public, sold))

    def test_python(self):
        self.exercise("python")

    @requires_rust
    def test_rust(self):
        self.exercise("rust")

    def exercise_legacy(self, kind: str) -> None:
        d = make_tmpdir(self, f"stamp-legacy-{kind}")
        c = new_constellation(d, kind, 1)
        store = os.path.join(d, f"witness.{kind}")
        daemon = Daemon(kind, c["keys"][0], c["registry"], c["cid"], store,
                        os.path.join(d, "witness.log"))
        self.addCleanup(daemon.stop)
        daemon.start()
        daemon.stop()
        # An old store may have sold stamps before public-key pinning existed.
        sidecar = store + ".stamps.json"
        old_public = load_mint(sidecar, bits=1024).public
        daemon.args = ["--stamps"]
        daemon.start()
        self.assertEqual(RemoteWitness(daemon.url).stamps.public, old_public)
        daemon.stop()
        os.rename(sidecar, sidecar + ".saved")
        failed = run_cli(daemon.command())
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("missing stamp key", failed.stdout + failed.stderr)

    def test_python_legacy_sidecar(self):
        self.exercise_legacy("python")

    @requires_rust
    def test_rust_legacy_sidecar(self):
        self.exercise_legacy("rust")


class FirstActivationTests(unittest.TestCase):
    def exercise(self, kind: str) -> None:
        d = make_tmpdir(self, f"stamp-activation-{kind}")
        c = new_constellation(d, kind, 1)
        store = os.path.join(d, f"witness.{kind}")
        daemon = Daemon(kind, c["keys"][0], c["registry"], c["cid"], store,
                        os.path.join(d, "witness.log"), args=["--adopt"])
        self.addCleanup(daemon.stop)
        daemon.start()
        daemon.stop()
        # An awaiting-ADOPT witness has no member but may have sold stamps.
        daemon.args = ["--stamps"]
        failed = run_cli(daemon.command())
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("missing stamp key", failed.stdout + failed.stderr)
        self.assertFalse(os.path.exists(store + ".stamps.json"))
        # A dangling sidecar symlink must not be followed or replaced when creating a key.
        sidecar = store + ".stamps.json"
        os.symlink(os.path.join(d, "missing-target"), sidecar)
        try:
            failed = run_cli(daemon.command() + ["--init-stamps"])
            self.assertNotEqual(failed.returncode, 0)
            self.assertTrue(os.path.islink(sidecar))
        finally:
            os.unlink(sidecar)
        daemon.args = ["--stamps", "--init-stamps"]
        daemon.start()
        self.assertIsNotNone(RemoteWitness(daemon.url).stamps)
        daemon.stop()
        daemon.args = ["--stamps"]
        daemon.start()  # after first activation, --init-stamps is no longer needed

    def test_python(self):
        self.exercise("python")

    @requires_rust
    def test_rust(self):
        self.exercise("rust")

    def test_redeemed_legacy_store_cannot_initialize_new_key(self):
        d = make_tmpdir(self, "stamp-redeemed-legacy-python")
        c = new_constellation(d, "redeemed", 1)
        store_path = os.path.join(d, "witness.db")
        store = WitnessStore(store_path)
        store.append([("stamp", "sold-and-redeemed", True)])
        store.close()
        daemon = Daemon("python", c["keys"][0], c["registry"], c["cid"], store_path,
                        os.path.join(d, "witness.log"), args=["--stamps", "--init-stamps"])
        failed = run_cli(daemon.command())
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("redeemed stamps exist", failed.stdout + failed.stderr)
        self.assertFalse(os.path.exists(store_path + ".stamps.json"))
