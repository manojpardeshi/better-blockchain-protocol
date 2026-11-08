"""Scenario 6: succession (SPEC §5.5) of a mixed constellation by a mixed successor committee.

Every witness process of the home is killed; after ``dead_man`` seconds without
heartbeats the committee signs the successor, new members adopt the committee's
mirror logs, and parcels homed there are spent again, including a payment that
was only partly voted when the home died. Then the old quorum comes back.
"""

import json
import signal
import unittest

from sigil import model
from sigil.charter import taken_over, verify_chain
from sigil.server import RemoteNetwork, RemoteStandby, RemoteWitness, RotationIncomplete
from sigil.wallet import SealFailed, Wallet, mirror_acks, request_seal
from tests.integration.harness import MIXED, IntegrationCase, manual_spend, poll

DEAD_MAN = 3


class SuccessionTests(IntegrationCase):
    def test_dead_home_is_succeeded_and_old_quorum_is_fenced(self):
        c = self.c
        S, old = c.constellation("heir", MIXED, committee=["python", "rust", "rust", "python"],
                                 dead_man=DEAD_MAN, start=False)
        H, h_idx = c.constellation("haven", ["rust", "python", "rust", "python"], start=False)
        ks = c.indices(S, role="standby")
        c.start_all(old + h_idx)
        members, committee = c.urls(old), None
        for i in ks:  # standby members probe the (now known) member URLs every half second
            c.witnesses[i]["args"] += ["--members", *members, "--probe-every", "0.5"]
        c.start_all(ks)
        committee = c.urls(ks)
        directory = {S: members, H: c.urls(h_idx)}
        net = self.net(directory, committees={S: committee})

        alice, carol = Wallet("alice", net, S), Wallet("carol", net, S)
        bob, dave, erin = (Wallet(n, net, H) for n in ("bob", "dave", "erin"))
        usd = alice.issue("USD", 1000)
        alice.pay(bob, usd, 100)                                        # S -> H, acks from both kinds
        alice.pay(carol, usd, 50)                                       # stays homed in S
        carol_ref = next(h["ref"] for h in carol.holdings.values())
        late_tid = alice.transact(*alice.payment_outputs(usd, 30, erin.address()))
        late_payment = alice.dossier.ancestry([late_tid])               # erin receives it after the takeover
        # A payment in flight when the home dies: mirrored and voted by only two members.
        header, body, _ = alice.prepare(*alice.payment_outputs(usd, 25, dave.address()))
        unlocks = alice.authorise(header, body)
        p = alice.dossier.output(body["inputs"][0])
        req = {"sigil": header["inputs"][0][0], "header": header, "home": S, "lock": p["lock"],
               "salt": p["salt"], "unlock": unlocks[header["inputs"][0][0]]}
        req["mirror"] = mirror_acks(net, req)
        self.assertEqual(len(req["mirror"]), 4)
        for w in net.witnesses(S)[:2]:
            w.spend(req)

        # The home dies: every witness process of S is killed.
        for i in old:
            c.kill(i, signal.SIGKILL)
        new = c.add_members(S, ["python", "rust", "rust", "python"], c.admin())
        nk = c.add_standbys(S, ["rust", "python", "rust", "python"], c.admin())
        c.start_all(new + nk)
        for i in new:
            c.witnesses[i]["pending"] = False
        new_urls, new_committee = c.urls(new), c.urls(nk)

        def takeover():
            try:
                return net.succeed(S, new_urls, c.token, committee_urls=new_committee, dead_man=DEAD_MAN)
            except RotationIncomplete:
                raise
            except RuntimeError:                       # a standby member's dead-man window is still open
                return None
        self.assertEqual(poll(takeover, timeout=DEAD_MAN + 30, interval=0.5, what="the takeover"), 1)
        chain = net.registry.chain(S)
        self.assertTrue(verify_chain(S, chain) and taken_over(chain, 0))
        self.assertTrue(all(RemoteStandby(u).info()["fenced"] for u in committee))
        self.assertEqual([w.version for w in net.witnesses(S)], [1] * 4)
        self.assertEqual({RemoteStandby(u).version for u in new_committee}, {1})

        # The in-flight payment completes under v1: its binding was in the committee's mirror logs.
        again_unlocks = alice.authorise(header, body)              # the same tid, re-authorised (SPEC §4 rule 1)
        alice.seal(header, body, again_unlocks)
        tid = alice.finalise(header, body, again_unlocks)
        seal = alice.dossier.seals[model.seal_key(req["sigil"], tid)]
        self.assertEqual(seal["version"], 1)
        dave.receive(alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
        # Parcels homed in S are spent again, and v0's history is deep-confirmed against v1.
        erin.receive(late_payment, [model.ref(late_tid, 0)])
        self.assertTrue(erin._confirmed, "history sealed by a succeeded version is deep-confirmed")
        carol.pay(bob, usd, 20)
        alice.pay(carol, usd, 5)
        bob.pay(alice, usd, 10)
        self.assertEqual({w.name: w.balance(usd) for w in (alice, bob, carol, dave, erin)},
                         {"alice": 800, "bob": 110, "carol": 35, "dave": 25, "erin": 30})

        # The old quorum comes back on its stores: still version 0 and unfrozen, but every standby
        # member that signed is fenced, so it collects no acks and votes on nothing new; and the
        # sigil carol spent under v1 cannot be spent again through it.
        # (They come back with the registry they had: version 0 only.)
        for i in old:
            c.start(i)
        for i in old:
            c.wait_ready(i)
        c.write_chain(S, chain)       # the operator records v1 for processes started from now on
        self.assertTrue(all(RemoteWitness(u).version == 0 for u in members))
        stale = RemoteNetwork({S: members, H: c.urls(h_idx)}, committees={S: committee}, timeout=10)
        e_addr = erin.address()
        hx, _bx, _ux, again = manual_spend(carol, [carol_ref], [model.parcel(S, usd, 50, e_addr["lock"], e_addr["salt"])])
        self.assertEqual(mirror_acks(stale, again[0]), [])
        with self.assertRaises(SealFailed):
            request_seal(stale, again[0])
        with self.assertRaises(SealFailed) as e:
            request_seal(net, again[0])
        self.assertEqual(len(e.exception.conflicts), 4)
        for u in members:
            st = RemoteWitness(u).status(again[0]["sigil"])
            self.assertNotIn(model.transition_id(hx), {v["tid"] for v in st["votes"]}, u)
        alice.pay(bob, usd, 1)                                          # the successor keeps serving
        self.check_invariants({w.name: w for w in (alice, bob, carol, dave, erin)}, headers=[hx])

    @unittest.expectedFailure
    def test_cli_wallet_spends_in_a_home_with_a_committee(self):
        """BUG (CLI, medium: parcels unspendable from the CLI, no safety loss): the command-line
        wallet cannot spend a parcel homed in a constellation whose charter names a successor
        committee.

        Scenario: S has a successor committee (``witnessd genesis --committee ... --dead-man``,
        a documented deployment, SPEC §5.5). alice (CLI wallet, home S) issues an asset and pays
        bob. Every witness of a version with a committee votes only with mirror acks from a
        quorum of the committee (SPEC §5.1), and the client collects them from the URLs in
        ``RemoteNetwork(committees=...)``. ``sigil/cli.py``'s ``_network`` builds
        ``RemoteNetwork(d.get("constellations", d))`` and the directory format (docs/WIRE.md
        "Files") has no place for committee URLs, so ``mirror_acks`` returns ``[]``, every
        witness answers "needs mirror acks from a quorum of the successor committee", and
        ``pay`` fails with SealFailed, leaving the parcel pledged until the authorisation
        expires (12 minutes by default). A CLI user can be paid into S but can never spend there.

        Suggested fix: accept ``{"constellations": {...}, "committees": {cid: [url, ...]}}`` in
        directory.json (and document it in WIRE.md "Files"), pass it as ``committees=`` in
        ``cli._network``, and have operators update it after a rotation or succession that
        changes the committee.
        """
        c = self.c
        S, old = c.constellation("heir", MIXED, committee=["python", "rust", "rust", "python"], dead_man=86400)
        ks = c.indices(S, role="standby")
        c.start_all(ks)
        self.write_directory({S: c.urls(old)})
        with open(self.directory_file) as f:
            d = json.load(f)
        d["committees"] = {S: c.urls(ks)}                               # the obvious place to say it
        with open(self.directory_file, "w") as f:
            json.dump(d, f)
        for who in ("alice", "bob"):
            self.cli(who, "init", "--home", S, "--name", who)
        usd = self.cli("alice", "issue", "USD", "100")["asset"]
        pay, _ = self.cli_pay("alice", "bob", usd, 10)
        self.cli("bob", "receive", pay)
