"""Holder-side validation: the receiver, not the network, checks *what*.

A *dossier* is everything needed to verify a parcel from the moment its
asset was created: the transitions in its ancestry, the seals binding
each consumed sigil, the owner unlocks, and the charters of every
constellation involved. Nobody else stores your history; you carry it,
and you hand the relevant part to whoever you pay.
"""

import json
from collections import Counter

from . import model
from .charter import Registry
from .locks import evaluate, well_formed
from .model import MINT_PREFIX, SELF_ASSET, SELF_MINT, base_asset, resolve_asset
from .proofs import verify_equivocation, verify_seal


class InvalidDossier(Exception):
    pass


class Dossier:
    def __init__(self):
        self.transitions: dict[str, dict] = {}   # tid -> {"header", "body", "unlocks"}
        self.seals: dict[str, dict] = {}         # "sigil:tid" -> seal
        self.charters: dict[str, list] = {}      # constellation id -> charter chain

    def add_transition(self, header: dict, body: dict, unlocks: dict) -> str:
        tid = model.transition_id(header)
        self.transitions[tid] = {"header": header, "body": body, "unlocks": unlocks}
        return tid

    def add_seal(self, seal: dict) -> None:
        self.seals[model.seal_key(seal["sigil"], seal["tid"])] = seal

    def add_charters(self, registry: Registry, cids) -> None:
        for cid in cids:
            chain = registry.chain(cid)
            if len(chain) > len(self.charters.get(cid, [])):
                self.charters[cid] = chain

    def merge(self, other: "Dossier") -> "Dossier":
        self.transitions.update(other.transitions)
        self.seals.update(other.seals)
        for cid, chain in other.charters.items():
            if len(chain) > len(self.charters.get(cid, [])):
                self.charters[cid] = chain
        return self

    def output(self, r: dict) -> dict:
        """The parcel created at ``r`` with its asset resolved (unverified)."""
        tx = self.transitions.get(r["tx"])
        if tx is None:
            raise InvalidDossier(f"missing transition {r['tx'][:12]}")
        outs = tx["body"]["outputs"]
        if not isinstance(r["i"], int) or not 0 <= r["i"] < len(outs):
            raise InvalidDossier("output index out of range")
        p = dict(outs[r["i"]])
        p["asset"] = resolve_asset(p["asset"], r["tx"])
        return p

    def ancestry(self, tids) -> "Dossier":
        """The minimal sub-dossier needed to verify outputs of ``tids``."""
        out, stack = Dossier(), list(tids)
        while stack:
            tid = stack.pop()
            if tid in out.transitions:
                continue
            tx = self.transitions[tid]
            out.transitions[tid] = tx
            for (s, _), r in zip(tx["header"]["inputs"], tx["body"]["inputs"]):
                key = model.seal_key(s, tid)
                if key in self.seals:
                    out.seals[key] = self.seals[key]
                stack.append(r["tx"])
        homes = {o["home"] for tx in out.transitions.values() for o in tx["body"]["outputs"]}
        out.charters = {c: ch for c, ch in self.charters.items() if c in homes}
        return out

    def to_json(self) -> str:
        return json.dumps({"transitions": self.transitions, "seals": self.seals, "charters": self.charters}, sort_keys=True)

    @classmethod
    def from_json(cls, data: str) -> "Dossier":
        obj, d = json.loads(data), cls()
        d.transitions, d.seals, d.charters = obj["transitions"], obj["seals"], obj["charters"]
        return d

    def __len__(self):
        return len(self.transitions)


class TrustPolicy:
    """A holder's own security assumptions.

    There is no global security parameter in Sigil: each holder decides
    which constellations it believes are honest-majority, and keeps a list
    of witnesses convicted of equivocation whose votes no longer count.
    """

    def __init__(self, registry: Registry | None = None, trusted=None):
        self.registry = registry or Registry()
        self.trusted = set(trusted) if trusted is not None else None  # None: trust any known charter
        self.convicted: set[str] = set()
        self.epoch = 0

    def trusts(self, cid: str) -> bool:
        return cid in self.registry and (self.trusted is None or cid in self.trusted)

    def trust(self, cid: str) -> None:
        if self.trusted is not None:
            self.trusted.add(cid)
        self.epoch += 1

    def convict(self, proof: dict) -> bool:
        if not verify_equivocation(proof):
            return False
        self.convicted.add(proof["a"]["witness"])
        self.epoch += 1
        return True


def _amount_ok(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool) and x > 0


class Verifier:
    """Verifies parcels against a trust policy, remembering what it has seen.

    Verified transitions are cached, so a holder never re-verifies history
    it already accepted: the cost of receiving a payment is proportional to
    the history that is *new to you*, not to the age of the asset.
    """

    def __init__(self, policy: TrustPolicy):
        self.policy = policy
        self._ok: set[str] = set()
        self._epoch = policy.epoch

    def verify_parcel(self, dossier: Dossier, r: dict) -> dict:
        for cid, chain in dossier.charters.items():
            try:
                self.policy.registry.add_chain(cid, chain)  # ignores chains we already know
            except ValueError as e:
                raise InvalidDossier(str(e)) from e
        self.verify_transition(dossier, r["tx"])
        return dossier.output(r)

    def verify_transition(self, dossier: Dossier, tid: str) -> None:
        if self._epoch != self.policy.epoch:  # trust changed: re-verify from scratch
            self._ok.clear()
            self._epoch = self.policy.epoch
        stack = [tid]
        while stack:
            cur = stack[-1]
            if cur in self._ok:
                stack.pop()
                continue
            tx = dossier.transitions.get(cur)
            if tx is None:
                raise InvalidDossier(f"missing transition {cur[:12]}")
            try:
                pending = [r["tx"] for r in tx["body"]["inputs"] if r["tx"] not in self._ok]
            except (KeyError, TypeError) as e:
                raise InvalidDossier("malformed inputs") from e
            if pending:
                stack.extend(pending)
                continue
            self._check(dossier, cur, tx)
            self._ok.add(cur)
            stack.pop()

    def _check(self, d: Dossier, tid: str, tx: dict) -> None:
        try:
            h, b, unlocks = tx["header"], tx["body"], tx["unlocks"]
            if model.transition_id(h) != tid or model.body_hash(b) != h["body"]:
                raise InvalidDossier("transition does not match its id")
            outputs = b["outputs"]
            if not outputs or not all(self._parcel_ok(o) for o in outputs):
                raise InvalidDossier("malformed output")
            if b["genesis"] is not None:
                return self._check_genesis(b, h)
            self._check_spend(d, tid, h, b, unlocks)
        except (KeyError, TypeError, ValueError) as e:
            raise InvalidDossier(f"malformed transition: {e}") from e

    @staticmethod
    def _parcel_ok(o: dict) -> bool:
        return (
            isinstance(o, dict) and set(o) == {"home", "asset", "amount", "lock", "salt"}
            and isinstance(o["home"], str) and isinstance(o["asset"], str) and isinstance(o["salt"], str)
            and _amount_ok(o["amount"]) and well_formed(o["lock"])
        )

    @staticmethod
    def _check_genesis(b: dict, h: dict) -> None:
        g = b["genesis"]
        if b["inputs"] or h["inputs"]:
            raise InvalidDossier("genesis cannot consume inputs")
        if not isinstance(g, dict) or not _amount_ok(g.get("supply")) or not isinstance(g.get("name"), str):
            raise InvalidDossier("malformed asset charter")
        if any(o["asset"] not in (SELF_ASSET, SELF_MINT) for o in b["outputs"]):
            raise InvalidDossier("genesis may only create its own asset")
        if sum(o["amount"] for o in b["outputs"]) != g["supply"]:
            raise InvalidDossier("genesis outputs must equal declared supply")

    def _check_spend(self, d: Dossier, tid: str, h: dict, b: dict, unlocks: dict) -> None:
        refs = b["inputs"]
        if not refs or len(refs) != len(h["inputs"]):
            raise InvalidDossier("inputs do not match header")
        if len({model.parcel_id(r) for r in refs}) != len(refs):
            raise InvalidDossier("duplicate input")
        if len({s for s, _ in h["inputs"]}) != len(h["inputs"]):
            raise InvalidDossier("duplicate sigil")
        totals_in, totals_out = Counter(), Counter()
        for r, (s, gen) in zip(refs, h["inputs"]):
            p = d.output(r)
            if model.sigil_of(p) != s:
                raise InvalidDossier("header sigil does not match input parcel")
            seal = d.seals.get(model.seal_key(s, tid))
            if seal is None:
                raise InvalidDossier(f"input {s[:12]} is not sealed")
            if seal["gen"] != gen or seal["constellation"] != p["home"]:
                raise InvalidDossier("seal does not match the input's home or generation")
            if not self.policy.trusts(p["home"]):
                raise InvalidDossier(f"untrusted constellation {p['home'][:12]}")
            if not verify_seal(seal, self.policy.registry, self.policy.convicted):
                raise InvalidDossier("seal lacks a quorum of valid votes")
            # Witnesses cannot steal: even a fully corrupt quorum cannot
            # produce the owner's unlock.
            if not evaluate(p["lock"], unlocks.get(s, {}), s, tid, None):
                raise InvalidDossier("owner did not authorise this spend")
            totals_in[p["asset"]] += p["amount"]
        for o in b["outputs"]:
            if o["asset"] in (SELF_ASSET, SELF_MINT):
                raise InvalidDossier("asset placeholders are only valid in genesis")
            totals_out[o["asset"]] += o["amount"]
        for asset in set(totals_in) | set(totals_out):
            x = base_asset(asset)
            m = MINT_PREFIX + x
            if totals_in[x] + totals_in[m] != totals_out[x] + totals_out[m]:
                raise InvalidDossier(f"value not conserved for {x[:12]}")
            if totals_out[m] > totals_in[m]:
                raise InvalidDossier("mint right cannot grow")
