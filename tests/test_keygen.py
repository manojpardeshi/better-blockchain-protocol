"""Key generation must never silently replace a witness identity."""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from sigil.witnessd import generate_key, load_key


ROOT = Path(__file__).resolve().parents[1]


class KeygenTests(unittest.TestCase):
    def test_python_cli_preserves_existing_pair(self):
        with tempfile.TemporaryDirectory() as d:
            key = Path(d) / "w.json"
            pub = Path(d) / "w.pub"
            first = generate_key(str(key))
            original = (key.read_bytes(), pub.read_bytes())

            result = subprocess.run([sys.executable, "-m", "sigil.witnessd", "keygen", "--out", str(key)],
                                    cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("exists", result.stderr)
            self.assertEqual((key.read_bytes(), pub.read_bytes()), original)
            self.assertEqual(load_key(str(key)).pk, first.pk)
            self.assertEqual(os.stat(key).st_mode & 0o777, 0o600)

            pub.unlink()
            missing_pub = subprocess.run([sys.executable, "-m", "sigil.witnessd", "keygen", "--out", str(key)],
                                         cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(missing_pub.returncode, 0)
            self.assertEqual(key.read_bytes(), original[0])
            self.assertFalse(pub.exists())

    def test_python_cli_preserves_lone_public_file(self):
        with tempfile.TemporaryDirectory() as d:
            key = Path(d) / "w.json"
            pub = Path(d) / "w.pub"
            pub.write_text("reserved\n")
            result = subprocess.run([sys.executable, "-m", "sigil.witnessd", "keygen", "--out", str(key)],
                                    cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("refusing to replace", result.stderr)
            self.assertFalse(key.exists())
            self.assertEqual(pub.read_text(), "reserved\n")

    def test_docker_init_recovers_partial_setup_without_replacing_keys(self):
        with tempfile.TemporaryDirectory() as d:
            env = dict(os.environ, NET=d, N="2", NAME="orion", PYTHONPATH=str(ROOT))
            command = ["sh", str(ROOT / "testnet" / "docker-init.sh")]

            def init():
                return subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)

            first = init()
            self.assertEqual(first.returncode, 0, first.stderr)
            key1, key2 = Path(d) / "keys/w1.json", Path(d) / "keys/w2.json"
            pub1, pub2 = Path(d) / "keys/w1.pub", Path(d) / "keys/w2.pub"
            original_keys = (key1.read_bytes(), key2.read_bytes())
            original_cid = (Path(d) / "cid").read_text()

            (Path(d) / "cid").unlink()
            pub1.unlink()  # interruption after private key creation
            second = init()
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual((key1.read_bytes(), key2.read_bytes()), original_keys)
            self.assertEqual(pub1.read_text().strip(), load_key(str(key1)).pk)
            self.assertEqual((Path(d) / "cid").read_text(), original_cid)

            (Path(d) / "cid").unlink()
            pub2.write_text("wrong key\n")
            third = init()
            self.assertNotEqual(third.returncode, 0)
            self.assertIn("does not match", third.stderr)
            self.assertEqual((key1.read_bytes(), key2.read_bytes()), original_keys)
            self.assertEqual(pub2.read_text(), "wrong key\n")

            pub2.write_text(load_key(str(key2)).pk + "\n")
            key2.unlink()
            fourth = init()
            self.assertNotEqual(fourth.returncode, 0)
            self.assertIn("refusing to replace a witness identity", fourth.stderr)
            self.assertFalse(key2.exists())


if __name__ == "__main__":
    unittest.main()
