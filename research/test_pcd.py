"""Tests for the PCD reference (research/pcd.py).

They pin down the integration seams before a real proving system exists:
the step relation means exactly what SPEC §6 / ``sigil.validate`` means, a
statement is constant-size and carries what a holder's *own* policy needs
(homes, charters, slack against convictions, deep confirmation), and a
holder verifying a proof object touches only constant-size data.

Run:  python3 -m unittest research.test_pcd -v
"""

import copy
import os
import random
import unittest

from research.pcd import (
    HolderPolicy, IdealBackend, InputWitness, ProofObject, ProofRejected, Statement, StepInvalid,
    TranscriptBackend, gather_confirmations, output_commitment, prove_history, step, witness_for,
)
from sigil import InvalidDossier, KeyPair, Network, TrustPolicy, Verifier, Wallet, model
from sigil.charter import Registry, charter_body
from sigil.swap import atomic_swap
from sigil.validate import Dossier

FUZZ = int(os.environ.get("SIGIL_PCD_FUZZ", "150"))


def received(wallet: Wallet, tid: str, i: int = 0) -> tuple[dict, dict]:
    """(ref, opening) of output ``i`` of ``tid``, as the payee knows it."""
    r = model.ref(tid, i)
    return r, wallet.dossier.output(r)


class World:
    """Two constellations, three wallets, two assets: payments, merges, a swap, a mint."""

    def __init__(self):
        self.net = Network()
        self.X = self.net.create_constellation("orion", 4)
        self.Y = self.net.create_constellation("lyra", 4)
        self.alice = Wallet("alice", self.net, self.X)
        self.bob = Wallet("bob", self.net, self.Y)
        self.carol = Wallet("carol", self.net, self.X)
        self.usd = self.alice.issue("USD", 1_000)
        self.gold = self.bob.issue("GOLD", 50, mint_cap=10)
        self.t = {}
        self.t["pay"] = self.alice.pay(self.bob, self.usd, 300)                 # X -> Y
        self.t["hop"] = self.bob.pay(self.carol, self.usd, 120)                 # Y -> X
        for _ in range(4):
            self.alice.pay(self.carol, self.usd, 10)
        self.t["merge"] = self.carol.pay(self.alice, self.usd, 155, home=self.Y)  # 5 inputs
        self.t["swap"] = atomic_swap(self.alice, self.usd, 100, self.bob, self.gold, 5)
        self.t["mint"] = self.bob.mint(self.gold, 3)

    def holder(self, **kw) -> HolderPolicy:
        return HolderPolicy(self.net.registry, **kw)


class StepAgreesWithValidate(unittest.TestCase):
    """Honest histories: the PCD verdict equals the dossier verdict, on both backends."""

    @classmethod
    def setUpClass(cls):
        cls.w = World()

    def check(self, wallet, tid, i=0):
        w = self.w
        d = wallet.dossier.ancestry([tid])
        ref, opening = received(wallet, tid, i)
        expected = Verifier(TrustPolicy(w.net.registry)).verify_parcel(d, ref)
        for backend in (TranscriptBackend(), IdealBackend()):
            proofs = prove_history(backend, d, [tid], w.net.registry)
            got = w.holder().accepts(backend, proofs[tid], ref, opening)
            self.assertEqual(got, expected, backend.name)

    def test_payment(self):
        self.check(self.w.bob, self.w.t["pay"])

    def test_hop_across_constellations(self):
        self.check(self.w.carol, self.w.t["hop"])

    def test_merge_of_five_inputs(self):
        self.check(self.w.alice, self.w.t["merge"])

    def test_swap_both_legs(self):
        self.check(self.w.alice, self.w.t["swap"], 0)
        self.check(self.w.alice, self.w.t["swap"], 1)

    def test_mint(self):
        self.check(self.w.bob, self.w.t["mint"])

    def test_statement_outputs_relied_homes(self):
        w = self.w
        d = w.alice.dossier.ancestry([w.t["swap"]])
        st = prove_history(IdealBackend(), d, [w.t["swap"]], w.net.registry)[w.t["swap"]].statement
        homes = {dict(r)["cid"] for r in st.relied}
        self.assertEqual(homes, {w.X, w.Y})  # the swap spends inputs homed in both
        self.assertTrue(all(dict(r)["slack"] == 1 for r in st.relied))  # n=4, all 4 votes, q=3
        self.assertEqual(st.excluded, ())
        tx = d.transitions[w.t["swap"]]
        self.assertEqual(len(st.outputs), len(tx["body"]["outputs"]))


class ConstantSize(unittest.TestCase):
    def test_statement_and_proof_do_not_grow_with_history(self):
        net = Network()
        homes = [net.create_constellation("orion", 4), net.create_constellation("lyra", 4)]
        issuer = Wallet("issuer", net, homes[0])
        asset = issuer.issue("USD", 1_000)
        backend, proofs, holder, sizes, dossier_bytes = IdealBackend(), {}, issuer, {}, {}
        for h in range(1, 41):
            nxt = Wallet(f"w{h}", net, homes[h % 2])
            tid = holder.pay(nxt, asset, 1_000)
            holder = nxt
            d = holder.dossier.ancestry([tid])
            prove_history(backend, d, [tid], net.registry, proofs=proofs)  # one new step per hop
            ref, opening = received(holder, tid)
            before = backend.verify_calls
            HolderPolicy(net.registry).accepts(backend, proofs[tid], ref, opening)
            self.assertEqual(backend.verify_calls - before, 1)  # the holder checks one proof, not a history
            sizes[h] = proofs[tid].size(backend)
            dossier_bytes[h] = len(d.to_json())
        self.assertEqual(backend.prove_calls, 41)  # genesis + 40 hops: each transition proven once
        self.assertEqual(sizes[2], sizes[40])       # constant once both homes are in the history
        self.assertGreater(dossier_bytes[40], 15 * dossier_bytes[2])
        self.assertLess(sizes[40], 1_200)


class CatchesInvalidHistories(unittest.TestCase):
    def setUp(self):
        self.w = World()

    def prove(self, d, tid, **kw):
        return prove_history(IdealBackend(), d, [tid], self.w.net.registry, **kw)

    def test_inflation_cannot_be_proven(self):
        w = self.w
        refs, _ = w.alice.select(w.usd, 10)
        addr = w.bob.address()
        # Blind witnesses seal it; holders (and the step) refuse it.
        tid = w.alice.transact(refs, [model.parcel(w.Y, w.usd, 9_999, addr["lock"], addr["salt"])])
        d = w.alice.dossier.ancestry([tid])
        with self.assertRaises(InvalidDossier):
            Verifier(TrustPolicy(w.net.registry)).verify_parcel(d, model.ref(tid, 0))
        with self.assertRaisesRegex(StepInvalid, "not conserved"):
            self.prove(d, tid)

    def test_missing_seal(self):
        w = self.w
        tid = w.t["hop"]
        d = copy.deepcopy(w.carol.dossier.ancestry([tid]))
        s = d.transitions[tid]["header"]["inputs"][0][0]
        del d.seals[model.seal_key(s, tid)]
        with self.assertRaises(InvalidDossier):
            Verifier(TrustPolicy(w.net.registry)).verify_parcel(d, model.ref(tid, 0))
        with self.assertRaises(StepInvalid):
            self.prove(d, tid)

    def test_seal_short_of_quorum(self):
        w = self.w
        tid = w.t["hop"]
        d = copy.deepcopy(w.carol.dossier.ancestry([tid]))
        s = d.transitions[tid]["header"]["inputs"][0][0]
        d.seals[model.seal_key(s, tid)]["votes"] = d.seals[model.seal_key(s, tid)]["votes"][:2]
        with self.assertRaisesRegex(StepInvalid, "quorum"):
            self.prove(d, tid)

    def test_owner_did_not_authorise(self):
        w = self.w
        tid = w.t["pay"]
        d = copy.deepcopy(w.bob.dossier.ancestry([tid]))
        s = d.transitions[tid]["header"]["inputs"][0][0]
        sigs = d.transitions[tid]["unlocks"][s]["sigs"]
        pk = next(iter(sigs))
        sigs[pk] = KeyPair.generate().sign("unlock", {"sigil": s, "tid": tid})  # someone else's key
        with self.assertRaises(InvalidDossier):
            Verifier(TrustPolicy(w.net.registry)).verify_parcel(d, model.ref(tid, 0))
        with self.assertRaisesRegex(StepInvalid, "authorise"):
            self.prove(d, tid)

    def test_input_must_match_parent_statement(self):
        w = self.w
        tid = w.t["hop"]
        d = w.carol.dossier.ancestry([tid])
        proofs = self.prove(d, tid)
        wit = witness_for(d, tid, w.net.registry)
        wit.inputs[0] = InputWitness(dict(wit.inputs[0].parcel, amount=10**9), wit.inputs[0].seal, wit.inputs[0].charter)
        parent = d.transitions[tid]["body"]["inputs"][0]["tx"]
        with self.assertRaisesRegex(StepInvalid, "not an output of its parent"):
            step(wit, {parent: proofs[parent].statement})

    def test_missing_parent_proof(self):
        w = self.w
        tid = w.t["hop"]
        d = w.carol.dossier.ancestry([tid])
        with self.assertRaisesRegex(StepInvalid, "no proof for parent"):
            step(witness_for(d, tid, w.net.registry), {})

    def test_fake_charter_for_version_zero(self):
        w = self.w
        tid = w.t["pay"]
        d = w.bob.dossier.ancestry([tid])
        proofs = self.prove(d, tid)
        wit = witness_for(d, tid, w.net.registry)
        fake = charter_body("orion", 0, [KeyPair.generate().pk for _ in range(4)], None)
        wit.inputs[0] = InputWitness(wit.inputs[0].parcel, wit.inputs[0].seal, fake)
        parent = d.transitions[tid]["body"]["inputs"][0]["tx"]
        with self.assertRaisesRegex(StepInvalid, "constellation id"):
            step(wit, {parent: proofs[parent].statement})

    def test_forged_proof_object(self):
        w = self.w
        tid = w.t["pay"]
        ref, opening = received(w.bob, tid)
        backend = IdealBackend()
        real = self.prove(w.bob.dossier.ancestry([tid]), tid)[tid]  # made with a different key
        rich = dict(opening, amount=10**9)
        forged = ProofObject(Statement(tid=tid, outputs=(output_commitment(tid, 0, rich),) + real.statement.outputs[1:],
                                       relied=real.statement.relied, excluded=()), b"\0" * 32)
        with self.assertRaisesRegex(ProofRejected, "does not verify"):
            w.holder().accepts(backend, forged, ref, rich)

    def test_wrong_opening(self):
        w = self.w
        tid = w.t["pay"]
        backend = IdealBackend()
        proof = prove_history(backend, w.bob.dossier.ancestry([tid]), [tid], w.net.registry)[tid]
        ref, opening = received(w.bob, tid)
        with self.assertRaisesRegex(ProofRejected, "not committed"):
            w.holder().accepts(backend, proof, ref, dict(opening, amount=opening["amount"] + 1))
        with self.assertRaisesRegex(ProofRejected, "not an output"):
            w.holder().accepts(backend, proof, model.ref("00" * 32, 0), opening)


class PolicyIsTheHolders(unittest.TestCase):
    """The same proof is accepted or refused according to each holder's own policy."""

    def setUp(self):
        self.w = World()
        self.backend = IdealBackend()
        tid = self.tid = self.w.t["hop"]  # usd: genesis (X) -> bob (Y) -> carol (X)
        self.proof = prove_history(self.backend, self.w.carol.dossier.ancestry([tid]), [tid], self.w.net.registry)[tid]
        self.ref, self.opening = received(self.w.carol, tid)

    def test_untrusted_home_in_ancestry(self):
        w = self.w
        only_x = w.holder(trusted={w.X})
        with self.assertRaisesRegex(ProofRejected, "untrusted constellation"):
            only_x.accepts(self.backend, self.proof, self.ref, self.opening)
        # The dossier verifier agrees.
        with self.assertRaises(InvalidDossier):
            Verifier(TrustPolicy(w.net.registry, {w.X})).verify_parcel(w.carol.dossier.ancestry([self.tid]), self.ref)
        w.holder(trusted={w.X, w.Y}).accepts(self.backend, self.proof, self.ref, self.opening)

    def test_unknown_charter_version(self):
        w = self.w
        partial = Registry()
        partial.add_chain(w.Y, w.net.registry.chain(w.Y))  # knows lyra, not orion
        with self.assertRaisesRegex(ProofRejected, "untrusted|do not know"):
            HolderPolicy(partial).accepts(self.backend, self.proof, self.ref, self.opening)

    def test_convictions_use_up_slack(self):
        w = self.w
        members = w.net.registry.latest(w.X)["witnesses"]
        d = w.carol.dossier.ancestry([self.tid])
        for k, ok in ((1, True), (2, False)):
            convicted = set(members[:k])
            tp = TrustPolicy(w.net.registry)
            tp.convicted = set(convicted)
            dossier_ok = True
            try:
                Verifier(tp).verify_parcel(d, self.ref)
            except InvalidDossier:
                dossier_ok = False
            self.assertEqual(dossier_ok, ok)
            pcd_ok = True
            try:
                w.holder(convicted=convicted).accepts(self.backend, self.proof, self.ref, self.opening)
            except ProofRejected:
                pcd_ok = False
            self.assertEqual(pcd_ok, ok, f"{k} convicted")

    def test_prover_can_exclude_convicted_witnesses(self):
        w = self.w
        one = w.net.registry.latest(w.X)["witnesses"][:1]
        d = w.carol.dossier.ancestry([self.tid])
        proof = prove_history(self.backend, d, [self.tid], w.net.registry, excluded=set(one))[self.tid]
        rows = [dict(r) for r in proof.statement.relied]
        self.assertTrue(all(r["slack"] == 0 for r in rows if r["cid"] == w.X))
        w.holder(convicted=set(one)).accepts(self.backend, proof, self.ref, self.opening)
        two = w.net.registry.latest(w.X)["witnesses"][:2]
        with self.assertRaisesRegex(StepInvalid, "quorum"):
            prove_history(IdealBackend(), d, [self.tid], w.net.registry, excluded=set(two))


class DeepConfirmation(unittest.TestCase):
    def setUp(self):
        self.w = World()
        self.tid = self.w.t["hop"]
        self.d = self.w.carol.dossier.ancestry([self.tid])
        self.ref, self.opening = received(self.w.carol, self.tid)

    def test_confirmed_history_and_staleness(self):
        w, backend = self.w, IdealBackend()
        conf = gather_confirmations(w.net, self.d, [self.tid])
        proof = prove_history(backend, self.d, [self.tid], w.net.registry, confirmations=conf)[self.tid]
        strict = w.holder(require_confirmed=True)
        strict.accepts(backend, proof, self.ref, self.opening)
        # Without confirmations the same holder refuses.
        plain = prove_history(backend, self.d, [self.tid], w.net.registry)[self.tid]
        with self.assertRaisesRegex(ProofRejected, "not deep-confirmed"):
            strict.accepts(backend, plain, self.ref, self.opening)
        # After orion rotates, confirmations by its old charter are stale.
        w.net.rotate(w.X, [KeyPair.generate() for _ in range(4)])
        with self.assertRaisesRegex(ProofRejected, "stale"):
            strict.accepts(backend, proof, self.ref, self.opening)
        w.holder(require_confirmed=True, confirm_lag=1).accepts(backend, proof, self.ref, self.opening)
        # Re-confirming against the new charter works: rotation hands bindings over.
        fresh = gather_confirmations(w.net, self.d, [self.tid])
        proof2 = prove_history(backend, self.d, [self.tid], w.net.registry, confirmations=fresh)[self.tid]
        strict.accepts(backend, proof2, self.ref, self.opening)

    def test_too_few_attestations(self):
        w = self.w
        conf = gather_confirmations(w.net, self.d, [self.tid])
        for c in conf.values():
            c["attestations"] = c["attestations"][:1]  # f = 1: need f + 1 = 2
        with self.assertRaisesRegex(StepInvalid, "f\\+1"):
            prove_history(IdealBackend(), self.d, [self.tid], w.net.registry, confirmations=conf)


class DifferentialFuzz(unittest.TestCase):
    """Random mutations of real dossiers: the PCD and dossier verdicts always agree."""

    MUTATIONS = ("amount", "drop_seal", "drop_vote", "unlock", "salt", "asset", "gen", "home", "memo", "genesis_supply")

    @staticmethod
    def mutate(rng, raw: dict, kind: str) -> None:
        txs = raw["transitions"]
        tid = rng.choice(sorted(txs))
        tx = txs[tid]
        if kind == "amount" and tx["body"]["outputs"]:
            o = rng.choice(tx["body"]["outputs"])
            o["amount"] += rng.choice([1, -1, 1000])
        elif kind == "drop_seal" and raw["seals"]:
            del raw["seals"][rng.choice(sorted(raw["seals"]))]
        elif kind == "drop_vote" and raw["seals"]:
            s = raw["seals"][rng.choice(sorted(raw["seals"]))]
            s["votes"] = s["votes"][: rng.randint(0, len(s["votes"]))]
        elif kind == "unlock" and tx["unlocks"]:
            u = tx["unlocks"][rng.choice(sorted(tx["unlocks"]))]
            for pk in u["sigs"]:
                u["sigs"][pk] = "00" * 64
        elif kind == "salt" and tx["body"]["outputs"]:
            rng.choice(tx["body"]["outputs"])["salt"] = "11" * 16
        elif kind == "asset" and tx["body"]["outputs"]:
            rng.choice(tx["body"]["outputs"])["asset"] = rng.choice(sorted(txs))
        elif kind == "gen" and tx["header"]["inputs"]:
            rng.choice(tx["header"]["inputs"])[1] += 1
        elif kind == "home" and tx["body"]["outputs"]:
            o = rng.choice(tx["body"]["outputs"])
            o["home"] = rng.choice([h for h in raw["charters"]])
        elif kind == "memo":
            tx["body"]["memo"] = "changed"
        elif kind == "genesis_supply" and tx["body"]["genesis"]:
            tx["body"]["genesis"]["supply"] += 1

    def test_verdicts_agree(self):
        w = World()
        cases = [(w.bob, w.t["pay"], 0), (w.carol, w.t["hop"], 0), (w.alice, w.t["merge"], 0),
                 (w.alice, w.t["swap"], 0), (w.alice, w.t["swap"], 1), (w.bob, w.t["mint"], 0)]
        rng = random.Random(1234)
        rejected = 0
        for n in range(FUZZ):
            wallet, tid, i = cases[n % len(cases)]
            base = wallet.dossier.ancestry([tid])
            raw = copy.deepcopy({"transitions": base.transitions, "seals": base.seals, "charters": base.charters})
            self.mutate(rng, raw, rng.choice(self.MUTATIONS))
            d = Dossier()
            d.transitions, d.seals, d.charters = raw["transitions"], raw["seals"], raw["charters"]
            ref = model.ref(tid, i)
            try:
                Verifier(TrustPolicy(w.net.registry)).verify_parcel(d, ref)
                dossier_ok = True
            except InvalidDossier:
                dossier_ok = False
            try:
                backend = IdealBackend()
                proofs = prove_history(backend, d, [tid], w.net.registry)
                HolderPolicy(w.net.registry).accepts(backend, proofs[tid], ref, d.output(ref))
                pcd_ok = True
            except (StepInvalid, ProofRejected, InvalidDossier, KeyError, TypeError, AttributeError):
                pcd_ok = False
            self.assertEqual(pcd_ok, dossier_ok, f"mutation #{n} disagrees")
            rejected += not dossier_ok
        self.assertGreater(rejected, FUZZ // 3)  # the mutations do bite


if __name__ == "__main__":
    unittest.main()
