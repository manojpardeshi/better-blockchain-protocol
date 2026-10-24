"""Proof-carrying data (PCD) for Sigil: a faithful *non-ZK* reference.

Today a holder receives a *dossier* (a parcel's whole ancestry) and runs
SPEC §6 on every transition in it. With recursive proofs it receives
instead one constant-size proof object per transition, which attests that
the transition is valid *and* that every input came out of a transition
that itself had such a proof. This module fixes the shape of that design
before any proving system exists:

* ``step(witness, children)`` is the per-transition relation: the SPEC §6
  validity predicate for one transition, plus the checks that bind its
  inputs to the public outputs of the children's proofs. It is exactly
  what a zkVM guest program (or circuit) must compute; see
  docs/research/RECURSIVE_PROOFS.md §8 for its pseudo-code.
* ``Statement`` is the public output of a proof. It never mentions the
  ancestry, only: the transition id, one hiding commitment per output, the
  charters whose seals the history relied on (with a vote "slack" each),
  the witnesses whose votes were excluded, and an optional deep-confirmation
  summary. Trust is *not* decided inside the proof: the holder applies its
  own policy to the statement (``HolderPolicy.accepts``).
* ``Backend`` is the pluggable succinct proving system. Two are provided:

  - ``TranscriptBackend``: the "proof" is the witness itself, and verifying
    it re-runs ``step`` recursively. This is today's dossier, recast as the
    trivial, non-succinct PCD instance (it is how the tests check that
    ``step`` agrees with ``sigil.validate``).
  - ``IdealBackend``: a mock of a succinct, zero-knowledge system. It only
    issues a proof after running ``step`` itself, and a proof is a 32-byte
    tag over (step id, statement digest). Verification checks the tag and
    nothing else: constant size, constant time, reveals nothing beyond the
    statement. It stands in for SP1/RISC Zero/Plonky2 until one is wired
    in; its key plays the role of soundness.

Nothing here changes the protocol: witnesses, seals, wallets and the wire
format are untouched. One *proposed* extension is modelled for deep
confirmation (``attest_binding``): a signed STATUS answer, which witnesses
do not produce today.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import secrets
from collections import Counter
from dataclasses import dataclass, field

try:
    from research import _compat  # noqa: F401  (sys.path, wallet shim)
except ImportError:  # pragma: no cover
    import _compat  # noqa: F401

from sigil import model
from sigil.charter import charter_hash, constellation_id, faults, quorum
from sigil.crypto import verify
from sigil.encoding import canonical, digest
from sigil.locks import evaluate, well_formed
from sigil.model import MINT_PREFIX, SELF_ASSET, SELF_MINT, base_asset, resolve_asset
from sigil.proofs import _counted_witnesses
from sigil.validate import Dossier

STEP_ID = digest("pcd-step", {"name": "sigil/v0 transition step", "spec": "SPEC §6 + docs/research/RECURSIVE_PROOFS.md §8"})
ATTEST_FIELDS = ("constellation", "version", "witness", "sigil", "gen", "tid", "time")
UNCONFIRMED = -1


class StepInvalid(Exception):
    """The step relation does not hold: no proof can exist for this transition."""


class ProofRejected(Exception):
    """A holder refuses a proof object (bad proof, wrong parcel, or policy)."""


# ---------------------------------------------------------------- statement

def output_commitment(tid: str, i: int, parcel: dict) -> str:
    """Hiding commitment to output ``i`` of ``tid`` (hiding through the parcel's salt).

    It also commits to the output's reference, so a child statement's
    outputs are bound to the transition that created them.
    """
    return digest("pcd-output", {"ref": model.ref(tid, i), "parcel": parcel})


@dataclass(frozen=True)
class Statement:
    """Public outputs of a proof for transition ``tid``.

    relied     sorted [{cid, version, charter, slack}]: every charter version
               whose seals the history relied on, the hash of that charter's
               body, and the minimum over those seals of (counted votes - quorum).
    excluded   sorted witness keys whose votes were *not* counted anywhere in
               the history (None: no seal at all, i.e. a lone genesis).
    confirmed  sorted [{cid, version, charter}]: the oldest charter version
               that deep-confirmed a consumption of that home (version -1:
               some consumption was not confirmed).
    """

    tid: str
    outputs: tuple
    relied: tuple = ()
    excluded: tuple | None = None
    confirmed: tuple = ()

    def to_json(self) -> dict:
        return {
            "v": STEP_ID, "tid": self.tid, "outputs": list(self.outputs),
            "relied": [dict(r) for r in self.relied],
            "excluded": None if self.excluded is None else list(self.excluded),
            "confirmed": [dict(c) for c in self.confirmed],
        }

    def digest(self) -> str:
        return digest("pcd-statement", self.to_json())

    def size(self) -> int:
        return len(canonical(self.to_json()))


def _freeze(rows: list) -> tuple:
    return tuple(tuple(sorted(r.items())) for r in rows)


def _rows(frozen: tuple) -> list:
    return [dict(r) for r in frozen]


# ------------------------------------------------------------------ witness

@dataclass
class InputWitness:
    """What the prover knows about input k of the transition being proven."""

    parcel: dict                 # the parent output, asset resolved (the opening)
    seal: dict                   # its seal to this transition
    charter: dict                # body of the charter version the seal claims
    confirmation: dict | None = None  # {"charter": body, "attestations": [...]} (optional)


@dataclass
class StepWitness:
    tid: str
    header: dict
    body: dict
    unlocks: dict
    inputs: list = field(default_factory=list)   # [InputWitness], aligned with body.inputs
    excluded: frozenset = frozenset()            # witnesses whose votes the prover will not count


def _amount_ok(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool) and x > 0


def _parcel_ok(o) -> bool:
    return (
        isinstance(o, dict) and set(o) == {"home", "asset", "amount", "lock", "salt"}
        and isinstance(o["home"], str) and isinstance(o["asset"], str) and isinstance(o["salt"], str)
        and _amount_ok(o["amount"]) and well_formed(o["lock"])
    )


class _OneCharter:
    """The registry interface ``proofs._counted_witnesses`` needs, for one charter."""

    def __init__(self, cid: str, body: dict):
        self.cid, self.body = cid, body

    def charter(self, cid: str, version: int):
        if cid == self.cid and isinstance(self.body, dict) and self.body.get("version") == version:
            return self.body
        return None


def _check_charter_claim(cid: str, body: dict) -> str:
    if not isinstance(body, dict) or not isinstance(body.get("witnesses"), list) or not body["witnesses"]:
        raise StepInvalid("malformed charter")
    # Version 0 *is* the constellation id; later versions are bound by hash
    # and checked against the holder's own registry (HolderPolicy).
    if body.get("version") == 0 and constellation_id(body) != cid:
        raise StepInvalid("charter version 0 does not match the constellation id")
    return charter_hash(body)


def verify_attestation(a: dict) -> bool:
    try:
        return verify(a["witness"], "attest", {k: a[k] for k in ATTEST_FIELDS}, a["sig"])
    except (KeyError, TypeError):
        return False


def _confirmed_version(cid: str, sigil: str, gen: int, tid: str, conf: dict | None) -> tuple[int, str | None]:
    """Deep confirmation (SPEC §9) of one consumption, from signed STATUS answers."""
    if conf is None:
        return UNCONFIRMED, None
    body = conf.get("charter")
    h = _check_charter_claim(cid, body)
    members = set(body["witnesses"])
    ok = set()
    for a in conf.get("attestations", []):
        if (isinstance(a, dict) and a.get("constellation") == cid and a.get("version") == body["version"]
                and a.get("sigil") == sigil and a.get("gen") == gen and a.get("tid") == tid
                and a.get("witness") in members and verify_attestation(a)):
            ok.add(a["witness"])
    if len(ok) <= faults(len(members)):
        raise StepInvalid("deep confirmation lacks f+1 current witnesses")
    return body["version"], h


def step(w: StepWitness, children: dict) -> Statement:
    """The per-transition relation: SPEC §6 for one transition, recursively.

    ``children`` maps each parent tid to the *statement* of its (already
    verified) proof. Raises ``StepInvalid`` if no proof may exist.
    """
    try:
        return _step(w, children)
    except (KeyError, TypeError, ValueError, AttributeError, IndexError, RecursionError) as e:
        raise StepInvalid(f"malformed witness: {type(e).__name__}") from e


def _step(w: StepWitness, children: dict) -> Statement:
    h, b, unlocks, tid = w.header, w.body, w.unlocks, w.tid
    # 1. hashes
    if model.transition_id(h) != tid or model.body_hash(b) != h["body"]:
        raise StepInvalid("transition does not match its id")
    # 2. outputs
    outs = b["outputs"]
    if not outs or not all(_parcel_ok(o) for o in outs):
        raise StepInvalid("malformed output")
    commitments = tuple(output_commitment(tid, i, dict(o, asset=resolve_asset(o["asset"], tid)))
                        for i, o in enumerate(outs))
    # 3. genesis
    if b["genesis"] is not None:
        g = b["genesis"]
        if b["inputs"] or h["inputs"]:
            raise StepInvalid("genesis cannot consume inputs")
        if not isinstance(g, dict) or not _amount_ok(g.get("supply")) or not isinstance(g.get("name"), str):
            raise StepInvalid("malformed asset charter")
        if any(o["asset"] not in (SELF_ASSET, SELF_MINT) for o in outs):
            raise StepInvalid("genesis may only create its own asset")
        if sum(o["amount"] for o in outs) != g["supply"]:
            raise StepInvalid("genesis outputs must equal declared supply")
        return Statement(tid=tid, outputs=commitments)
    # 4. spend
    refs = b["inputs"]
    if not refs or len(refs) != len(h["inputs"]) or len(w.inputs) != len(refs):
        raise StepInvalid("inputs do not match header")
    if len({model.parcel_id(r) for r in refs}) != len(refs):
        raise StepInvalid("duplicate input")
    if len({s for s, _ in h["inputs"]}) != len(h["inputs"]):
        raise StepInvalid("duplicate sigil")
    relied: dict[tuple, dict] = {}
    confirmed: dict[str, dict] = {}
    excluded = frozenset(w.excluded)

    def rely(cid, version, chash, slack):
        key = (cid, version)
        prev = relied.get(key)
        if prev is not None and prev["charter"] != chash:
            raise StepInvalid("two different charters claimed for one version")
        if prev is None or slack < prev["slack"]:
            relied[key] = {"cid": cid, "version": version, "charter": chash, "slack": slack}

    def confirm(cid, version, chash):
        prev = confirmed.get(cid)
        if prev is None or version < prev["version"]:
            confirmed[cid] = {"cid": cid, "version": version, "charter": chash}

    totals_in, totals_out = Counter(), Counter()
    for r, (s, gen), iw in zip(refs, h["inputs"], w.inputs):
        child = children.get(r["tx"])
        if child is None:
            raise StepInvalid(f"no proof for parent {str(r['tx'])[:12]}")
        p = iw.parcel
        if not _parcel_ok(p) or not 0 <= r["i"] < len(child.outputs):
            raise StepInvalid("malformed input opening")
        # The input exists and is valid: it is committed by the parent's statement.
        if output_commitment(r["tx"], r["i"], p) != child.outputs[r["i"]]:
            raise StepInvalid("input is not an output of its parent's proof")
        if model.sigil_of(p) != s:
            raise StepInvalid("header sigil does not match input parcel")
        seal = iw.seal
        if (not isinstance(seal, dict) or seal.get("sigil") != s or seal.get("tid") != tid
                or seal.get("gen") != gen or seal.get("constellation") != p["home"]):
            raise StepInvalid("seal does not match the input's sigil, home or generation")
        chash = _check_charter_claim(p["home"], iw.charter)
        counted, charter = _counted_witnesses(model.votes_of_seal(seal), _OneCharter(p["home"], iw.charter), excluded)
        if charter is None:
            raise StepInvalid("seal does not name the supplied charter")
        q = quorum(len(charter["witnesses"]))
        if len(counted) < q:
            raise StepInvalid("seal lacks a quorum of valid votes")
        rely(p["home"], charter["version"], chash, len(counted) - q)
        # Witnesses cannot steal: re-check the owner's authorisation.
        if not evaluate(p["lock"], unlocks.get(s, {}), s, tid, None):
            raise StepInvalid("owner did not authorise this spend")
        v, ch = _confirmed_version(p["home"], s, gen, tid, iw.confirmation)
        confirm(p["home"], v, ch)
        totals_in[p["asset"]] += p["amount"]
    # 5. conservation
    for o in outs:
        if o["asset"] in (SELF_ASSET, SELF_MINT):
            raise StepInvalid("asset placeholders are only valid in genesis")
        totals_out[o["asset"]] += o["amount"]
    for asset in set(totals_in) | set(totals_out):
        x = base_asset(asset)
        m = MINT_PREFIX + x
        if totals_in[x] + totals_in[m] != totals_out[x] + totals_out[m]:
            raise StepInvalid(f"value not conserved for {x[:12]}")
        if totals_out[m] > totals_in[m]:
            raise StepInvalid("mint right cannot grow")
    # Fold in the children's public outputs (each distinct parent once).
    for ptid in {r["tx"] for r in refs}:
        c = children[ptid]
        for row in _rows(c.relied):
            rely(row["cid"], row["version"], row["charter"], row["slack"])
        for row in _rows(c.confirmed):
            confirm(row["cid"], row["version"], row["charter"])
        if c.excluded is not None:
            excluded = excluded & frozenset(c.excluded)
    return Statement(
        tid=tid, outputs=commitments,
        relied=_freeze(sorted(relied.values(), key=lambda r: (r["cid"], r["version"]))),
        excluded=tuple(sorted(excluded)),
        confirmed=_freeze(sorted(confirmed.values(), key=lambda r: r["cid"])),
    )


# ----------------------------------------------------------------- backends

@dataclass
class ProofObject:
    """What travels with a parcel instead of a dossier."""

    statement: Statement
    pi: object  # backend-specific; constant size for a succinct backend

    def size(self, backend: "Backend") -> int:
        return self.statement.size() + backend.proof_size(self.pi)


class Backend:
    """A proving system for the step relation (the succinct-verifier seam)."""

    name = "abstract"

    def prove(self, w: StepWitness, children: dict) -> ProofObject:
        raise NotImplementedError

    def verify(self, proof: ProofObject) -> bool:
        raise NotImplementedError

    def proof_size(self, pi) -> int:
        raise NotImplementedError


class TranscriptBackend(Backend):
    """Non-succinct PCD: the proof *is* the witness plus the children's proofs.

    Verifying re-runs ``step`` all the way down, so this is today's dossier
    in PCD form: same cost, same leakage, and a cross-check that ``step``
    means what ``sigil.validate`` means.
    """

    name = "transcript"

    def prove(self, w, children_proofs: dict) -> ProofObject:
        if not all(self.verify(p) for p in children_proofs.values()):
            raise StepInvalid("a child proof does not verify")
        st = step(w, {t: p.statement for t, p in children_proofs.items()})
        return ProofObject(st, {"witness": w, "children": children_proofs})

    def verify(self, proof: ProofObject) -> bool:
        seen: dict[int, bool] = {}

        def rec(p: ProofObject) -> bool:
            if id(p) in seen:
                return seen[id(p)]
            try:
                kids = p.pi["children"]
                ok = all(rec(c) for c in kids.values()) and step(
                    p.pi["witness"], {t: c.statement for t, c in kids.items()}) == p.statement
            except (StepInvalid, KeyError, TypeError, AttributeError):
                ok = False
            seen[id(p)] = ok
            return ok

        return rec(proof)

    def proof_size(self, pi) -> int:
        total, stack, seen = 0, [pi], set()
        while stack:
            x = stack.pop()
            if id(x) in seen:
                continue
            seen.add(id(x))
            w = x["witness"]
            total += len(canonical({"header": w.header, "body": w.body, "unlocks": w.unlocks,
                                    "inputs": [vars(i) for i in w.inputs]}))
            stack.extend(c.pi for c in x["children"].values())
        return total


class IdealBackend(Backend):
    """Mock of a succinct zero-knowledge proving system.

    ``prove`` runs the step relation (after checking every child proof) and
    returns a 32-byte tag; ``verify`` checks the tag only. Whoever lacks the
    key cannot make a tag, which models soundness; the tag says nothing
    about the witness, which models zero knowledge. Swap in a real backend
    behind the same three methods.
    """

    name = "ideal"
    PROOF_BYTES = 32

    def __init__(self, key: bytes | None = None):
        self._key = key or secrets.token_bytes(32)
        self.prove_calls = 0
        self.verify_calls = 0

    def _tag(self, st: Statement) -> bytes:
        return hmac.new(self._key, (STEP_ID + st.digest()).encode(), hashlib.blake2b).digest()[:self.PROOF_BYTES]

    def prove(self, w, children_proofs: dict) -> ProofObject:
        self.prove_calls += 1
        if not all(self.verify(p) for p in children_proofs.values()):
            raise StepInvalid("a child proof does not verify")
        st = step(w, {t: p.statement for t, p in children_proofs.items()})
        return ProofObject(st, self._tag(st))

    def verify(self, proof: ProofObject) -> bool:
        self.verify_calls += 1
        return isinstance(proof.pi, bytes) and hmac.compare_digest(proof.pi, self._tag(proof.statement))

    def proof_size(self, pi) -> int:
        return self.PROOF_BYTES


# ----------------------------------------------------------------- holders

class HolderPolicy:
    """A holder's trust policy, applied to a statement instead of a dossier.

    ``registry`` and ``trusted`` are those of ``sigil.validate.TrustPolicy``;
    ``convicted`` is the holder's own conviction list; ``require_confirmed``
    asks for deep confirmation by each home's *current* charter, up to
    ``confirm_lag`` versions old.
    """

    def __init__(self, registry, trusted=None, convicted=(), require_confirmed: bool = False, confirm_lag: int = 0):
        self.registry = registry
        self.trusted = None if trusted is None else set(trusted)
        self.convicted = set(convicted)
        self.require_confirmed = require_confirmed
        self.confirm_lag = confirm_lag

    @classmethod
    def of(cls, trust_policy, **kw) -> "HolderPolicy":
        return cls(trust_policy.registry, trust_policy.trusted, trust_policy.convicted, **kw)

    def trusts(self, cid: str) -> bool:
        return cid in self.registry and (self.trusted is None or cid in self.trusted)

    def check_statement(self, st: Statement) -> None:
        excluded = None if st.excluded is None else set(st.excluded)
        for row in _rows(st.relied):
            cid, v = row["cid"], row["version"]
            if not self.trusts(cid):
                raise ProofRejected(f"history relies on untrusted constellation {cid[:12]}")
            body = self.registry.charter(cid, v)
            if body is None or charter_hash(body) != row["charter"]:
                raise ProofRejected(f"history relies on a charter {cid[:12]}/v{v} we do not know")
            # Convictions the prover did not already exclude eat into the slack.
            fresh = (self.convicted - (excluded or set())) & set(body["witnesses"])
            if len(fresh) > row["slack"]:
                raise ProofRejected(f"convicted witnesses invalidate seals of {cid[:12]}/v{v}")
        if self.require_confirmed:
            conf = {r["cid"]: r for r in _rows(st.confirmed)}
            for row in _rows(st.relied):
                c = conf.get(row["cid"])
                latest = self.registry.latest(row["cid"])
                if c is None or c["version"] == UNCONFIRMED:
                    raise ProofRejected(f"history not deep-confirmed at {row['cid'][:12]}")
                body = self.registry.charter(row["cid"], c["version"])
                if body is None or charter_hash(body) != c["charter"]:
                    raise ProofRejected("confirmation by a charter we do not know")
                if latest["version"] - c["version"] > self.confirm_lag:
                    raise ProofRejected(f"deep confirmation at {row['cid'][:12]} is stale")

    def accepts(self, backend: Backend, proof: ProofObject, ref: dict, parcel: dict) -> dict:
        """Verify a received parcel from its proof object alone (constant-size data)."""
        if not backend.verify(proof):
            raise ProofRejected("proof does not verify")
        st = proof.statement
        if ref.get("tx") != st.tid or not isinstance(ref.get("i"), int) or not 0 <= ref["i"] < len(st.outputs):
            raise ProofRejected("reference is not an output of this proof")
        if output_commitment(st.tid, ref["i"], parcel) != st.outputs[ref["i"]]:
            raise ProofRejected("parcel is not committed by the proof")
        self.check_statement(st)
        if not self.trusts(parcel["home"]):
            raise ProofRejected("parcel lives in a constellation we do not trust")
        return parcel


# ------------------------------------------------------------------ provers

def witness_for(dossier: Dossier, tid: str, registry, excluded=frozenset(), confirmations=None) -> StepWitness:
    """Assemble the step witness for ``tid`` from a dossier the prover holds.

    In a deployment the prover holds only its own inputs' openings and the
    parents' proof objects; a dossier is just a convenient source here.
    """
    tx = dossier.transitions[tid]
    inputs = []
    for r, (s, _g) in zip(tx["body"]["inputs"], tx["header"]["inputs"]):
        p = dossier.output(r)
        seal = dossier.seals.get(model.seal_key(s, tid))
        charter = registry.charter(p["home"], seal["version"]) if isinstance(seal, dict) else None
        conf = (confirmations or {}).get((s, tid))
        inputs.append(InputWitness(parcel=p, seal=seal, charter=charter, confirmation=conf))
    return StepWitness(tid=tid, header=tx["header"], body=tx["body"], unlocks=tx["unlocks"],
                       inputs=inputs, excluded=frozenset(excluded))


def topological(dossier: Dossier, tids) -> list:
    """Ancestry of ``tids`` in dependency order (parents first)."""
    order, state, stack = [], {}, [(t, False) for t in tids]
    while stack:
        t, done = stack.pop()
        if done:
            if state.get(t) != "done":
                state[t] = "done"
                order.append(t)
            continue
        if state.get(t) is not None:
            continue
        state[t] = "open"
        stack.append((t, True))
        for r in dossier.transitions[t]["body"]["inputs"]:
            if state.get(r["tx"]) is None:
                stack.append((r["tx"], False))
    return order


def prove_history(backend: Backend, dossier: Dossier, tids, registry, *, excluded=frozenset(),
                  confirmations=None, proofs: dict | None = None) -> dict:
    """Prove every transition in the ancestry of ``tids`` bottom-up; tid -> ProofObject.

    ``proofs`` holds proofs already made (each transition is proven once,
    by whoever creates it: the cost per payment is one step).
    """
    proofs = {} if proofs is None else proofs
    for t in topological(dossier, tids):
        if t in proofs:
            continue
        w = witness_for(dossier, t, registry, excluded, confirmations)
        kids = {r["tx"]: proofs[r["tx"]] for r in w.body["inputs"]}
        proofs[t] = backend.prove(w, kids)
    return proofs


# ------------------------------------------------- proposed: signed STATUS

def attest_binding(witness, sigil: str) -> dict | None:
    """A *proposed* extension: a witness signs its current binding of ``sigil``.

    Deep confirmation (SPEC §9) asks current witnesses for STATUS; inside a
    proof, those answers must be signed so the step can check them. Returns
    None if the witness holds no binding.
    """
    rec = witness.records.get(sigil)
    if rec is None or rec.tid is None or witness.cid is None:
        return None
    a = {"constellation": witness.cid, "version": witness.version, "witness": witness.pk,
         "sigil": sigil, "gen": rec.gen, "tid": rec.tid, "time": int(witness.clock())}
    a["sig"] = witness.kp.sign("attest", a)
    return a


def gather_confirmations(network, dossier: Dossier, tids) -> dict:
    """Signed STATUS answers from each home's current charter, per (sigil, tid)."""
    out = {}
    for t in topological(dossier, tids):
        tx = dossier.transitions[t]
        for r, (s, _g) in zip(tx["body"]["inputs"], tx["header"]["inputs"]):
            home = dossier.output(r)["home"]
            body = network.registry.latest(home)
            atts = [a for a in (attest_binding(w, s) for w in network.witnesses(home)
                                if w.pk in set(body["witnesses"])) if a is not None]
            out[(s, t)] = {"charter": body, "attestations": atts}
    return out


def statement_json(st: Statement) -> str:
    return json.dumps(st.to_json(), sort_keys=True)
