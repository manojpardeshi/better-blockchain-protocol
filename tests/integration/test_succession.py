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
from sigil.swap import propose_swap
from sigil.wallet import SealFailed, Wallet, find_death_proof, mirror_acks, request_seal
from tests.integration.harness import MIXED, IntegrationCase, manual_spend, poll

DEAD_MAN = 3


class SuccessionTests(IntegrationCase):
    def committee_home(self, peer_kinds: list) -> tuple:
        """S (mixed) with a mixed successor committee whose members probe S's members, plus a
        peer constellation; both exist before any process starts. Returns (S, P, net, old)."""
        c = self.c
        S, old = c.constellation("heir", MIXED, committee=["python", "rust", "rust", "python"],
                                 dead_man=DEAD_MAN, start=False)
        P, p_idx = c.constellation("peer", peer_kinds, start=False)
        ks = c.indices(S, role="standby")
        c.start_all(old + p_idx)
        for i in ks:  # standby members probe the (now known) member URLs every half second
            c.witnesses[i]["args"] += ["--members", *c.urls(old), "--probe-every", "0.5"]
        c.start_all(ks)
        self.committee = c.urls(ks)
        self.standby_idx = ks
        net = self.net({S: c.urls(old), P: c.urls(p_idx)}, committees={S: self.committee})
        return S, P, net, old

    def kill_and_succeed(self, net, S: str, old: list) -> list:
        """Kill every witness of S, then have its committee sign version 1 for four new
        members and a new committee, polling until the dead-man period has passed."""
        c = self.c
        for i in old:
            c.kill(i, signal.SIGKILL)
        new = c.add_members(S, ["python", "rust", "rust", "python"], c.admin())
        nk = c.add_standbys(S, ["rust", "python", "rust", "python"], c.admin())
        c.start_all(new + nk)
        for i in new:
            c.witnesses[i]["pending"] = False

        def takeover():
            try:
                return net.succeed(S, c.urls(new), c.token, committee_urls=c.urls(nk), dead_man=DEAD_MAN)
            except RotationIncomplete:
                raise
            except RuntimeError:                       # a standby member's dead-man window is still open
                return None
        self.assertEqual(poll(takeover, timeout=DEAD_MAN + 30, interval=0.5, what="the takeover"), 1)
        return nk

    def test_dead_home_is_succeeded_and_old_quorum_is_fenced(self):
        c = self.c
        S, H, net, old = self.committee_home(["rust", "python", "rust", "python"])
        members, committee = c.urls(old), self.committee
        h_idx = c.indices(H)

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

        # The home dies: every witness process of S is killed, and its committee takes over.
        nk = self.kill_and_succeed(net, S, old)
        new_committee = c.urls(nk)
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

    def _sealed_then_betrayed(self, net, S: str, Y: str):
        """alice (home S) and mallory (home Y) agree a swap; alice's input is mirrored, voted and
        sealed to it, then mallory spends her own input elsewhere. Returns (alice, bob, usd, header)."""
        alice, mallory, bob = Wallet("alice", net, S), Wallet("mallory", net, Y), Wallet("bob", net, Y)
        usd, gold = alice.issue("USD", 100), mallory.issue("GOLD", 10)
        header, body, _ = propose_swap(alice, usd, 100, mallory, gold, 10)
        unlocks = {**alice.authorise(header, body), **mallory.authorise(header, body)}
        me = mallory.address()
        hb, bb, ub, betrayal = manual_spend(mallory, [body["inputs"][1]],
                                            [model.parcel(Y, gold, 10, me["lock"], me["salt"])])
        mallory.dossier.add_seal(request_seal(net, betrayal[0]))
        mallory.finalise(hb, bb, ub)
        with self.assertRaises(SealFailed):
            alice.seal(header, body, unlocks)
        self.wallets = {"alice": alice, "mallory": mallory, "bob": bob}
        return alice, bob, usd, header

    def test_abort_before_a_succession_survives_it(self):
        S, Y, net, old = self.committee_home(["rust", "python", "rust", "python"])
        alice, bob, usd, header = self._sealed_then_betrayed(net, S, Y)
        a_main, tid = header["inputs"][0][0], model.transition_id(header)
        proof = find_death_proof(net, header, tid, alice._parcels_for(header))
        # alice aborts: S's witnesses release her input, and the committee (Rust and Python
        # standby members) stores the release next to the binding it mirrored.
        self.assertEqual(alice.abort(header), [a_main])
        entry = {"kind": "release", "gen": 0, "tid": tid, "header": header, "proof": proof}
        for u in self.committee:
            self.assertIs(RemoteStandby(u).note_release(a_main, entry), False, "abort stored it already")
        self.kill_and_succeed(net, S, old)
        # The successor inherits the release: alice's input is free at generation 1.
        for w in net.witnesses(S):
            st = w.status(a_main)
            self.assertEqual((st["gen"], st["tid"]), (1, None), w)
        alice.pay(bob, usd, 100)
        self.assertEqual(bob.balance(usd), 100)
        self.check_invariants(self.wallets, headers=[header])

    def test_abort_survives_a_succession_when_the_committee_missed_the_release(self):
        """BUG (wallet, medium: funds stuck after a succession, no safety loss): an input aborted
        under the old version is unspendable under its successor if the committee never stored
        the release, and the wallet never presents its death proof again.

        Scenario: alice's input (home S, which has a successor committee) is mirrored, voted and
        sealed to a swap; mallory spends her own swap input elsewhere. alice ``abort``s while S's
        committee is unreachable (a transient outage): every S witness releases the input (it is
        free at generation 1), but ``abort``'s ``note_release`` to the committee fails silently
        (best effort). Then S dies and the committee takes over. The new members ADOPT the
        committee's mirror logs, which hold the generation-0 binding and no release, so they
        are bound to the dead swap at generation 0 (SPEC §5.5 "Accepted failure modes" expects
        such records to wait "until someone presents a death proof"). alice's wallet holds the
        parcel at generation 1, but it dropped the pledge, the pending swap and its header in
        ``abort``, so it can neither present the proof again nor rebuild it: every spend fails
        with "bound at an earlier generation; release it first".

        Suggested fix: keep the header and death proof of every aborted transition (in
        ``wallet_store``) until a quorum of the home's *current* members reports the input past
        that generation; when a spend is refused as "bound at an earlier generation" (or before
        spending a parcel whose home was rotated or succeeded since the abort), RELEASE again at
        the current members with the stored proof. Optionally make ``abort`` retry
        ``note_release`` until a committee quorum has stored it.
        """
        c = self.c
        S, Y, net, old = self.committee_home(["rust", "python", "rust", "python"])
        alice, bob, usd, header = self._sealed_then_betrayed(net, S, Y)
        for i in self.standby_idx:
            c.kill(i, signal.SIGKILL)                    # the committee is briefly unreachable
        self.assertEqual(alice.abort(header), [header["inputs"][0][0]])
        for i in self.standby_idx:
            c.start(i)
        for i in self.standby_idx:
            c.wait_ready(i)
        self.kill_and_succeed(net, S, old)
        alice.pay(bob, usd, 100)
