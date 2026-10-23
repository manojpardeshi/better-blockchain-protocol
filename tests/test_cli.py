"""The command-line wallet, driven against witnesses served over real HTTP."""

import io
import json
import os
import stat
import tempfile
import unittest
from contextlib import redirect_stderr

from sigil import Network, cli, wallet_store
from sigil.server import RemoteNetwork, WitnessServer


class CliTests(unittest.TestCase):
    def setUp(self):
        self.sim = Network()
        self.X = self.sim.create_constellation("orion")
        self.servers = [WitnessServer(w).start() for w in self.sim.all_witnesses(self.X)]
        self.addCleanup(lambda: [s.stop() for s in self.servers])
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.d = tmp.name
        self.directory = os.path.join(self.d, "directory.json")
        with open(self.directory, "w") as f:
            json.dump({"constellations": {self.X: [s.url for s in self.servers]}}, f)

    def path(self, name):
        return os.path.join(self.d, name)

    def run_cli(self, who, *argv, ok=True):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stderr(err):
            code = cli.main(["--wallet", self.path(who), "--directory", self.directory, *argv], out=out)
        self.assertEqual(code == 0, ok, err.getvalue())
        return json.loads(out.getvalue()) if ok else json.loads(err.getvalue())

    def address_file(self, who):
        addr = self.run_cli(who, "address")
        p = self.path(f"{who}-addr-{addr['salt'][:8]}.json")
        with open(p, "w") as f:
            json.dump(addr, f)
        return p

    def balance(self, who, asset):
        return self.run_cli(who, "balance", asset)[asset]

    def test_alice_bob_carol(self):
        for who in ("alice", "bob", "carol"):
            self.run_cli(who, "init", "--home", self.X, "--name", who)
        asset = self.run_cli("alice", "issue", "USD", "1000")["asset"]
        self.assertEqual(self.run_cli("alice", "assets"), [{"asset": asset, "name": "USD", "balance": 1000}])

        pay1 = self.path("pay1.json")
        r = self.run_cli("alice", "pay", self.address_file("bob"), asset, "300", "--out", pay1)
        self.assertEqual(r["balance"], 700)
        got = self.run_cli("bob", "receive", pay1, "--deep")
        self.assertEqual(got["received"], [{"asset": asset, "amount": 300, "home": self.X}])

        # Receiving the same payment again is an idempotent no-op.
        self.assertTrue(self.run_cli("bob", "receive", pay1)["already"])
        self.assertEqual(self.balance("bob", asset), 300)

        pay2 = self.path("pay2.json")
        self.run_cli("bob", "pay", self.address_file("carol"), asset, "120", "--out", pay2)
        self.run_cli("carol", "receive", pay2)
        self.assertEqual([self.balance(w, asset) for w in ("alice", "bob", "carol")], [700, 180, 120])

        # Bob has since spent the parcel of pay1: replaying it is rejected (sigil consumed).
        self.assertEqual(self.run_cli("bob", "receive", pay1, ok=False)["error"], "InvalidDossier")

        # State survives a reload with a fresh network client.
        w = wallet_store.load(self.path("carol"), RemoteNetwork({self.X: [s.url for s in self.servers]}))
        self.assertEqual(w.balance(asset), 120)
        self.assertEqual(self.run_cli("carol", "export-dossier")["transitions"].keys(),
                         json.loads(w.dossier.to_json())["transitions"].keys())
        mode = stat.S_IMODE(os.stat(os.path.join(self.path("carol"), wallet_store.KEYS)).st_mode)
        self.assertEqual(mode, 0o600)

        # Carol can spend what she received after reloading.
        pay3 = self.path("pay3.json")
        self.run_cli("carol", "pay", self.address_file("alice"), asset, "20", "--out", pay3)
        self.run_cli("alice", "receive", pay3)
        self.assertEqual(self.balance("alice", asset), 720)

    def test_tampered_payment_rejected(self):
        for who in ("alice", "bob"):
            self.run_cli(who, "init", "--home", self.X)
        asset = self.run_cli("alice", "issue", "USD", "100")["asset"]
        pay = self.path("pay.json")
        self.run_cli("alice", "pay", self.address_file("bob"), asset, "10", "--out", pay)
        with open(pay) as f:
            obj = json.load(f)
        tid = obj["refs"][0]["tx"]
        obj["dossier"]["transitions"][tid]["body"]["outputs"][0]["amount"] = 99
        bad = self.path("bad.json")
        with open(bad, "w") as f:
            json.dump(obj, f)
        self.run_cli("bob", "receive", bad, ok=False)
        self.assertEqual(self.balance("bob", asset), 0)
        with open(bad, "w") as f:
            f.write("{not json")
        self.assertEqual(self.run_cli("bob", "receive", bad, ok=False)["error"], "CliError")
        self.run_cli("bob", "receive", pay)
        self.assertEqual(self.balance("bob", asset), 10)

    def test_errors(self):
        self.run_cli("alice", "balance", ok=False)                       # no wallet yet
        self.run_cli("alice", "init", "--home", self.X)
        self.run_cli("alice", "init", "--home", self.X, ok=False)        # already exists
        self.run_cli("zed", "init", "--home", "00" * 32, ok=False)       # unknown home
        asset = self.run_cli("alice", "issue", "USD", "5")["asset"]
        self.run_cli("alice", "pay", self.address_file("alice"), asset, "6",
                     "--out", self.path("p.json"), ok=False)              # insufficient funds


if __name__ == "__main__":
    unittest.main()
