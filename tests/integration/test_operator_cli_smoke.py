"""No-value operator drill with separate wallet processes and live witnesses."""

import json
import os
import signal
import subprocess
import sys
import tempfile
import unittest

from testnet.launcher import ROOT, Testnet


class OperatorCliSmokeTests(unittest.TestCase):
    def test_cross_constellation_payment_survives_witness_restart(self):
        with tempfile.TemporaryDirectory(prefix="sigil-operator-cli-") as directory:
            network = Testnet(os.path.join(directory, "network"))
            network.create(constellations=2, witnesses=4)
            try:
                network.start_all()
                home_alice, home_bob = list(network.directory())
                directory_file = network.path("directory.json")

                def wallet(name, *args):
                    command = [sys.executable, "-m", "sigil.cli", "--wallet",
                               os.path.join(directory, name), "--directory", directory_file,
                               *args]
                    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                            timeout=30, stdin=subprocess.DEVNULL)
                    self.assertEqual(result.returncode, 0,
                                     f"{command!r}: {result.stderr or result.stdout}")
                    return json.loads(result.stdout)

                wallet("alice", "init", "--home", home_alice)
                wallet("bob", "init", "--home", home_bob)
                asset = wallet("alice", "issue", "TEST", "10")["asset"]

                def pay_and_receive(amount, number):
                    address_file = os.path.join(directory, f"bob-address-{number}.json")
                    with open(address_file, "w") as stream:
                        json.dump(wallet("bob", "address"), stream)
                    payment = os.path.join(directory, f"payment-{number}.json")
                    wallet("alice", "pay", address_file, asset, str(amount), "--out", payment)
                    received = wallet("bob", "receive", payment, "--deep")
                    self.assertEqual(received["received"],
                                     [{"asset": asset, "amount": amount, "home": home_bob}])

                pay_and_receive(2, 1)
                network.kill(0, signal.SIGKILL)
                pay_and_receive(3, 2)  # one unavailable witness must not stop a quorum
                network.start(0)       # same key, store and port
                network.wait_ready(0)
                pay_and_receive(1, 3)
                self.assertEqual(wallet("alice", "balance", asset)[asset], 4)
                self.assertEqual(wallet("bob", "balance", asset)[asset], 6)
            finally:
                network.stop_all(signal.SIGKILL)


if __name__ == "__main__":
    unittest.main()
