"""A wallet: holds keys, parcels and dossiers; seals and verifies.

All protocol intelligence that a blockchain puts in the network lives
here: building transitions, gathering seals, validating what you receive,
and recovering parcels from failed multi-party transitions.
"""

import secrets
from collections import defaultdict

from . import locks, model
from .charter import faults, quorum
from .crypto import KeyPair
from .locks import keys_in, sign_unlock
from .network import Network
from .proofs import proves_dead, verify_seal, verify_vote
from .stamps import buy_stamp
from .validate import Dossier, InvalidDossier, TrustPolicy, Verifier
from .witness import Conflict, Rejected


class SealFailed(Exception):
    def __init__(self, sigil: str, votes: list, conflicts: list):
        super().__init__(f"could not seal {sigil[:12]}: {len(votes)} votes, {len(conflicts)} conflicting")
        self.sigil, self.votes, self.conflicts = sigil, votes, conflicts


def request_seal(network: Network, req: dict, stamp_for=None) -> dict:
    """Ask every witness of the sigil's home to vote; assemble a seal."""
    tid = model.transition_id(req["header"])
    gen = next(g for s, g in req["header"]["inputs"] if s == req["sigil"])
    by_version: dict[int, list] = defaultdict(list)
    conflicts = []
    for w in network.witnesses(req["home"]):
        r = dict(req)
        stamp = stamp_for(w) if stamp_for else None
        if stamp is not None:
            r["stamp"] = stamp
        try:
            v = w.spend(r)
        except Conflict as e:
            if e.vote is not None:
                conflicts.append(e.vote)
            continue
        except Rejected:
            continue
        if (verify_vote(v) and v["sigil"] == req["sigil"] and v["tid"] == tid
                and v["gen"] == gen and v["constellation"] == req["home"]):
            by_version[v["version"]].append(v)
    for version in sorted(by_version, reverse=True):
        votes = by_version[version]
        seal = model.seal_from_votes(votes)
        if verify_seal(seal, network.registry):
            return seal
    raise SealFailed(req["sigil"], [v for vs in by_version.values() for v in vs], conflicts)


def find_death_proof(network: Network, header: dict, tid: str, parcels: dict) -> dict | None:
    """Look for evidence that ``tid`` can never be sealed.

    ``parcels`` maps input sigils to their parcels (at least ``home``,
    ``lock`` and ``salt``); a proof can only cite an input whose parcel we
    know, because witnesses check the evidence comes from its home.
    """
    for s, g in header["inputs"]:
        if s not in parcels:
            continue
        p = parcels[s]
        target = {"home": p["home"], "lock": p["lock"], "salt": p["salt"]}
        votes = [v for v in network.find_votes(s) if v["gen"] == g and verify_vote(v)]
        groups: dict[tuple, dict] = defaultdict(dict)
        for v in votes:
            if v["tid"] != tid:
                groups[(v["constellation"], v["version"], v["tid"])][v["witness"]] = v
        for (cid, version, t), vs in groups.items():
            proof = {"kind": "seal", "sigil": s, "gen": g, "parcel": target,
                     "seal": model.seal_from_votes(list(vs.values()))}
            if proves_dead(header, tid, proof, network.registry):
                return proof
        others: dict[tuple, dict] = defaultdict(dict)
        for v in votes:
            if v["tid"] != tid:
                others[(v["constellation"], v["version"])][v["witness"]] = v
        for vs in others.values():
            proof = {"kind": "votes", "sigil": s, "gen": g, "parcel": target, "votes": list(vs.values())}
            if proves_dead(header, tid, proof, network.registry):
                return proof
    return None


class Wallet:
    def __init__(self, name: str, network: Network, home: str | None = None, *, trusted=None):
        self.name = name
        self.network = network
        self.home = home
        self.policy = TrustPolicy(network.registry, trusted)
        self.verifier = Verifier(self.policy)
        self.keys: dict[str, KeyPair] = {}
        self.dossier = Dossier()
        self.holdings: dict[str, dict] = {}   # parcel id -> {"ref", "parcel", "sigil", "gen"}
        self.pledged: dict[str, tuple] = {}   # sigil -> (gen, tid) we authorised; never sign twice
        self.stamps: dict[str, list] = defaultdict(list)

    def __repr__(self):
        return f"Wallet({self.name})"

    # ------------------------------------------------------------- receiving

    def fresh_key(self) -> KeyPair:
        kp = KeyPair.generate()
        self.keys[kp.pk] = kp
        return kp

    def address(self, home: str | None = None, lock: dict | None = None) -> dict:
        """A one-time receiving address: where the parcel lives and how it unlocks."""
        home = home or self.home
        return {"home": home, "lock": lock or locks.sig(self.fresh_key().pk), "salt": secrets.token_hex(16)}

    def receive(self, dossier: Dossier, refs: list) -> list:
        """Verify incoming parcels end-to-end and take custody of them."""
        received = []
        for r in refs:
            p = self.verifier.verify_parcel(dossier, r)
            if not self.policy.trusts(p["home"]):
                raise InvalidDossier("parcel lives in a constellation we do not trust")
            if not keys_in(p["lock"]) & set(self.keys):
                raise InvalidDossier("parcel is not addressed to us")
            s = model.sigil_of(p)
            bound = sum(1 for w in self.network.witnesses(p["home"]) if w.status(s)["tid"] is not None)
            if bound > faults(len(self.network.all_witnesses(p["home"]))):
                raise InvalidDossier("parcel's sigil is already consumed")
            self.dossier.merge(dossier)
            self.holdings[model.parcel_id(r)] = {"ref": r, "parcel": p, "sigil": s, "gen": 0}
            received.append(p)
        return received

    def watch(self, dossier: Dossier, r: dict) -> dict:
        """Track a parcel we may be able to unlock under some condition (e.g. a bond)."""
        p = self.verifier.verify_parcel(dossier, r)
        self.dossier.merge(dossier)
        self.holdings[model.parcel_id(r)] = {"ref": r, "parcel": p, "sigil": model.sigil_of(p), "gen": 0}
        return p

    def balance(self, asset: str) -> int:
        return sum(h["parcel"]["amount"] for h in self.holdings.values()
                   if h["parcel"]["asset"] == asset and keys_in(h["parcel"]["lock"]) & set(self.keys))

    # --------------------------------------------------------------- issuing

    def issue(self, name: str, supply: int, home: str | None = None, *, mint_cap: int = 0) -> str:
        """Create a new asset. Its id is the id of this genesis transition."""
        home = home or self.home
        a = self.address(home)
        outputs = [model.parcel(home, model.SELF_ASSET, supply, a["lock"], a["salt"])]
        if mint_cap:
            m = self.address(home)
            outputs.append(model.parcel(home, model.SELF_MINT, mint_cap, m["lock"], m["salt"]))
        b = model.body([], outputs, genesis={"name": name, "supply": supply + mint_cap})
        tid = self.dossier.add_transition(model.header([], b), b, {})
        self.dossier.add_charters(self.network.registry, [home])
        for i in range(len(outputs)):
            r = model.ref(tid, i)
            p = self.verifier.verify_parcel(self.dossier, r)
            self.holdings[model.parcel_id(r)] = {"ref": r, "parcel": p, "sigil": model.sigil_of(p), "gen": 0}
        return tid

    def mint(self, asset: str, amount: int, home: str | None = None) -> str:
        right = next((h for h in self.holdings.values() if h["parcel"]["asset"] == model.MINT_PREFIX + asset), None)
        if right is None:
            raise ValueError("no mint right for this asset")
        cap = right["parcel"]["amount"]
        if amount > cap:
            raise ValueError("exceeds remaining mint cap")
        a = self.address(home)
        outputs = [model.parcel(a["home"], asset, amount, a["lock"], a["salt"])]
        if cap > amount:
            m = self.address(right["parcel"]["home"])
            outputs.append(model.parcel(m["home"], model.MINT_PREFIX + asset, cap - amount, m["lock"], m["salt"]))
        return self.transact([right["ref"]], outputs, memo="mint")

    # --------------------------------------------------------------- spending

    def select(self, asset: str, amount: int) -> tuple[list, int]:
        picked, total = [], 0
        for h in sorted(self.holdings.values(), key=lambda h: -h["parcel"]["amount"]):
            if h["parcel"]["asset"] == asset and h["parcel"]["lock"]["op"] == "sig" and h["sigil"] not in self.pledged:
                picked.append(h["ref"])
                total += h["parcel"]["amount"]
                if total >= amount:
                    return picked, total
        raise ValueError(f"{self.name}: insufficient funds")

    def payment_outputs(self, asset: str, amount: int, to_address: dict) -> tuple[list, list]:
        refs, total = self.select(asset, amount)
        outputs = [model.parcel(to_address["home"], asset, amount, to_address["lock"], to_address["salt"])]
        if total > amount:
            c = self.address()
            outputs.append(model.parcel(c["home"], asset, total - amount, c["lock"], c["salt"]))
        return refs, outputs

    def pay(self, to: "Wallet", asset: str, amount: int, home: str | None = None) -> str:
        """Pay ``to``; the recipient chooses where the parcel lives (``home``)."""
        addr = to.address(home)
        refs, outputs = self.payment_outputs(asset, amount, addr)
        tid = self.transact(refs, outputs)
        to.receive(self.dossier.ancestry([tid]), [model.ref(tid, 0)])
        return tid

    def prepare(self, refs: list, outputs: list, memo: str = "", gens: dict | None = None) -> tuple[dict, dict, str]:
        """Build a transition. ``gens`` gives generations of inputs we do not hold."""
        b = model.body(refs, outputs, memo=memo)
        sigils = []
        for r in refs:
            s = model.sigil_of(self.dossier.output(r))
            h = self.holdings.get(model.parcel_id(r))
            sigils.append([s, h["gen"] if h else (gens or {}).get(s, 0)])
        hd = model.header(sigils, b)
        return hd, b, model.transition_id(hd)

    def authorise(self, header: dict, body: dict, extra: dict | None = None) -> dict:
        """Sign for our own inputs. Refuses to ever sign two spends of one sigil."""
        tid = model.transition_id(header)
        unlocks = {}
        for r, (s, g) in zip(body["inputs"], header["inputs"]):
            h = self.holdings.get(model.parcel_id(r))
            if h is None:
                continue
            prior = self.pledged.get(s)
            if prior is not None and prior[0] == g and prior[1] != tid:
                raise ValueError("refusing to equivocate: sigil already pledged")
            u = locks.empty_unlock()
            for pk in keys_in(h["parcel"]["lock"]) & set(self.keys):
                u["sigs"][pk] = sign_unlock(self.keys[pk], s, tid)
            unlocks[s] = locks.merge_unlocks(u, (extra or {}).get(s, {}))
            self.pledged[s] = (g, tid)
        return unlocks

    def seal(self, header: dict, body: dict, unlocks: dict) -> list:
        tid = model.transition_id(header)
        seals = []
        for r, (s, _g) in zip(body["inputs"], header["inputs"]):
            p = self.dossier.output(r)
            req = {"sigil": s, "header": header, "home": p["home"], "lock": p["lock"],
                   "salt": p["salt"], "unlock": unlocks.get(s, locks.empty_unlock())}
            seals.append(request_seal(self.network, req, self._stamp_for))
        for seal in seals:
            self.dossier.add_seal(seal)
        return seals

    def finalise(self, header: dict, body: dict, unlocks: dict) -> str:
        """Record a sealed transition and update holdings."""
        tid = self.dossier.add_transition(header, body, unlocks)
        homes = {o["home"] for o in body["outputs"]} | {self.dossier.output(r)["home"] for r in body["inputs"]}
        self.dossier.add_charters(self.network.registry, homes)
        for r in body["inputs"]:
            self.holdings.pop(model.parcel_id(r), None)
        for i, o in enumerate(body["outputs"]):
            if keys_in(o["lock"]) & set(self.keys):
                r = model.ref(tid, i)
                p = self.dossier.output(r)
                self.holdings[model.parcel_id(r)] = {"ref": r, "parcel": p, "sigil": model.sigil_of(p), "gen": 0}
        return tid

    def transact(self, refs: list, outputs: list, *, extra_unlocks: dict | None = None, memo: str = "") -> str:
        header, body, _ = self.prepare(refs, outputs, memo)
        unlocks = self.authorise(header, body, extra_unlocks)
        try:
            self.seal(header, body, unlocks)
        except SealFailed:
            for s, _g in header["inputs"]:
                self.unpledge_if_unbound(s)
            raise
        return self.finalise(header, body, unlocks)

    def unpledge_if_unbound(self, sigil: str) -> bool:
        """Drop a pledge only if every witness of the home provably holds no vote for it."""
        pledge = self.pledged.get(sigil)
        h = next((h for h in self.holdings.values() if h["sigil"] == sigil), None)
        if pledge is None or h is None:
            return False
        gen, tid = pledge
        for w in self.network.all_witnesses(h["parcel"]["home"]):
            if w.pk in self.network.down:
                return False  # unreachable: it might hold a vote
            st = w.status(sigil)
            if (st["gen"] == gen and st["tid"] == tid) or any(
                    v["gen"] == gen and v["tid"] == tid for v in st["votes"]):
                return False
        del self.pledged[sigil]
        return True

    # -------------------------------------------------------------- recovery

    def abort(self, header: dict) -> list:
        """Recover our inputs from a transition that can never complete."""
        tid = model.transition_id(header)
        proof = find_death_proof(self.network, header, tid, self._parcels_for(header))
        if proof is None:
            raise ValueError("no proof that the transition is dead")
        released = []
        for h in self.holdings.values():
            s = h["sigil"]
            if self.pledged.get(s, (None, None))[1] != tid:
                continue
            home = h["parcel"]["home"]
            gens = []
            for w in self.network.witnesses(home):
                try:
                    gens.append(w.release(s, proof))
                except Rejected:
                    pass
            if len(gens) >= quorum(len(self.network.all_witnesses(home))):
                h["gen"] = max(gens)
                del self.pledged[s]
                released.append(s)
        return released

    def _parcels_for(self, header: dict) -> dict:
        """The parcels behind a header's input sigils, as far as our dossier knows them."""
        wanted, found = {s for s, _ in header["inputs"]}, {}
        for tid, tx in self.dossier.transitions.items():
            for i in range(len(tx["body"]["outputs"])):
                p = self.dossier.output(model.ref(tid, i))
                s = model.sigil_of(p)
                if s in wanted:
                    found[s] = p
        return found

    # ----------------------------------------------------------------- stamps

    def buy_stamps(self, cid: str, count: int) -> None:
        for w in self.network.all_witnesses(cid):
            if w.stamps is not None:
                self.stamps[w.pk].extend(buy_stamp(w.stamps.public, w.sell_stamp) for _ in range(count))

    def _stamp_for(self, w):
        pool = self.stamps.get(w.pk)
        return pool.pop() if pool else None
