"""Scenario 5: rotating a live mixed constellation (admin token), with CLI wallets on both sides.

The operator rotates R from four old members (Rust and Python) to four new ones,
one of which re-uses an old Rust member's key in a Python process. Wallets keep
paying across the rotation and deep-confirm history sealed by both versions.
"""

import os

from sigil.server import RemoteNetwork, RemoteWitness
from tests.integration.harness import MIXED, IntegrationCase


class RotationTests(IntegrationCase):
    def test_rotation_of_a_live_constellation(self):
        c = self.c
        R, old = c.constellation("rotor", MIXED, start=False)
        H, h_idx = c.constellation("haven", ["python", "rust", "python", "rust"], start=False)
        c.start_all(old + h_idx)
        old_urls, h_urls = c.urls(old), c.urls(h_idx)
        self.write_directory({R: old_urls, H: h_urls})

        for who, home in (("alice", R), ("bob", H), ("carol", R), ("dave", R)):
            self.cli(who, "init", "--home", home, "--name", who)
        usd = self.cli("alice", "issue", "USD", "1000")["asset"]
        for payee, amount in (("bob", 100), ("carol", 50), ("dave", 30), ("dave", 10)):
            pay, _ = self.cli_pay("alice", payee, usd, amount)
            self.cli(payee, "receive", pay, "--deep")
        first_input = self.load_wallet("bob").dossier.transitions
        v0_sigils = {s for tx in first_input.values() for s, _g in tx["header"]["inputs"]}

        # Without the admin token nobody can rotate, and no member freezes.
        new_urls = self._new_members(R, old[0])
        operator = RemoteNetwork({R: old_urls}, timeout=10)
        with self.assertRaises(RuntimeError):
            operator.rotate(R, new_urls, "wrong-token")
        self.assertFalse(any(RemoteWitness(u)._get("info")["frozen"] for u in old_urls))
        # The operator rotates R; payments in flight elsewhere are unaffected.
        self.assertEqual(operator.rotate(R, new_urls, c.token), 1)
        c.write_chain(R, operator.registry.chain(R))
        for u in old_urls:
            info = RemoteWitness(u)._get("info")
            self.assertTrue(info["frozen"] and info["version"] == 0, u)
        for u in new_urls:
            self.assertEqual(RemoteWitness(u).version, 1)

        # A wallet still pointed at the old members cannot pay (they are frozen), and loses nothing.
        stale = self.write_directory({R: old_urls, H: h_urls}, self.file("stale-directory.json"))
        self.write_directory({R: new_urls, H: h_urls})
        err = self.cli("dave", "pay", self.address_file("bob"), usd, 25, "--out", self.file("x.json"),
                       directory=stale, ok=False)
        self.assertEqual(err["error"], "SealFailed")
        self.assertEqual(self.cli_balance("dave", usd), 40)

        # After the rotation: v1 seals, with history sealed by v0 deep-confirmed against v1.
        pay, _ = self.cli_pay("alice", "bob", usd, 70)                  # alice's change: sealed by v0, spent in v1
        self.cli("bob", "receive", pay, "--deep")
        pay, _ = self.cli_pay("carol", "bob", usd, 50)                  # a parcel made under v0, spent under v1
        self.cli("bob", "receive", pay, "--deep")
        pay, _ = self.cli_pay("dave", "carol", usd, 5)                  # dave's other parcel
        self.cli("carol", "receive", pay, "--deep")
        self.cli("erin", "init", "--home", R, "--name", "erin")         # a wallet born after the rotation
        pay, _ = self.cli_pay("alice", "erin", usd, 20)
        self.cli("erin", "receive", pay, "--deep")
        erin = self.load_wallet("erin")
        # alice's change chain runs through seals of both versions; v1's members confirmed them all.
        self.assertEqual({s["version"] for s in erin.dossier.seals.values()}, {0, 1})
        self.assertEqual(len(erin._confirmed), len(erin.dossier.seals))
        self.assertEqual(len(erin.network.registry.chain(R)), 2)

        # The re-used key (a Python process now) brought its Rust predecessor's votes: for every
        # input sealed under v0 it holds the same binding, and no other.
        reused = RemoteWitness(new_urls[0])
        self.assertEqual(reused.pk, RemoteWitness(old_urls[0]).pk)
        for s in v0_sigils:
            st = reused.status(s)
            if st["votes"]:
                self.assertEqual({v["tid"] for v in st["votes"]}, {st["tid"]}, s)
        self.assertTrue(any(v["version"] == 0 for s in v0_sigils for v in reused.status(s)["votes"]))

        balances = {w: self.cli_balance(w, usd) for w in ("alice", "bob", "carol", "dave", "erin")}
        self.assertEqual(balances, {"alice": 720, "bob": 220, "carol": 5, "dave": 35, "erin": 20})
        self.check_invariants({w: self.load_wallet(w) for w in ("alice", "bob", "carol", "dave", "erin")})

    def _new_members(self, cid: str, reuse: int) -> list:
        """Start four witnesses waiting for ADOPT; the first re-uses the key of witness ``reuse``."""
        c = self.c
        kinds = ["python", "rust", "rust", "python"]
        idx = c.add_members(cid, kinds, c.admin(), keys=[c.witnesses[reuse]["key"], None, None, None])
        c.start_all(idx)
        for i in idx:
            c.witnesses[i]["pending"] = False
        self.assertTrue(all(RemoteWitness(c.url(i)).cid is None for i in idx), "new members wait for ADOPT")
        self.assertTrue(os.path.exists(c.witnesses[idx[0]]["store"]))
        return c.urls(idx)
