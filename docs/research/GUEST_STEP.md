# Guest program spec: the per-transition step function

*Phase 3 (#10) research note. Companion to [RECURSIVE_PROOFS.md](RECURSIVE_PROOFS.md). Status: draft for the M1 port.*

This is the program a zkVM (SP1, RISC Zero, Jolt) runs once per transition. It is the SPEC §6 validity predicate for **one** transition, plus the checks that bind each input to the public statement of its parent's proof. Recursion means the guest never touches the ancestry, only the parents' *statements*.

Two executable versions already exist and agree byte-for-byte on the statement digest for every test vector:

* [`research/pcd.py`](../../research/pcd.py), `step()`: the Python reference, differentially tested against `sigil.validate`.
* [`research/rv32_cycles/guest`](../../research/rv32_cycles/guest/src/main.rs): a bare-metal RV32IM Rust program with the same logic, run in an instruction-counting emulator.

## Interface

```
image id        STEP_VK      hash of this program; also the statement field "v"
private input   W            the step witness (below)
public output   digest(Φ)    Φ = the statement (below), committed to the journal
recursion       verify(STEP_VK, digest(Φ_parent)) for each distinct parent
```

**Witness** `W`:

| Field | Content |
|---|---|
| `tid, header, body, unlocks` | the transition, as in a dossier |
| `inputs[k]` | `{parcel, seal, charter}`: the opening of input *k* (asset resolved), its seal to `tid`, and the charter body (`cid`, `version`) the seal claims |
| `inputs[k].confirmation` | optional: `{charter, attestations}` signed STATUS answers from the home's current charter (proposed extension, §6 of the design doc) |
| `excluded` | witness keys whose votes the prover will not count (convictions it knows about) |
| `children` | `{parent_tid: Φ_parent}`, the parents' statements |

**Statement** `Φ` (canonical encoding, hashed with tag `pcd-statement`):

```
Φ = { v:         STEP_VK,
      tid:       transition id,
      outputs:   [ H("pcd-output", {ref: {tx: tid, i}, parcel: output_i with asset resolved}) ],
      relied:    sorted [ {cid, version, charter: H("charter", body), slack} ],
      excluded:  sorted [ witness pk ]  or null (no seal anywhere: a lone genesis),
      confirmed: sorted [ {cid, version, charter} ]   version -1 = some consumption unconfirmed }
```

## Step function (pseudo-code)

```text
step(W) -> Φ:
  # 1. identity
  require H("transition", W.header) == W.tid
  require H("body", W.body) == W.header.body

  # 2. outputs
  require W.body.outputs non-empty, each well_formed_parcel (exact keys, amount > 0, lock well-formed:
          depth <= 8, <= 64 nodes, exact keys per op)
  outputs := [ H("pcd-output", {ref: {tx: W.tid, i}, parcel: resolve(o)}) for i, o in W.body.outputs ]

  # 3. genesis: no inputs, only "" / "mint:" assets, sum(amounts) == genesis.supply
  if W.body.genesis != null:
      check genesis rules
      return {v, tid, outputs, relied: [], excluded: null, confirmed: []}

  # 4. spend
  require body.inputs non-empty, |body.inputs| == |header.inputs| == |W.inputs|
  require distinct H("parcel", ref) over body.inputs; distinct sigils over header.inputs
  relied := {}; confirmed := {}; E := set(W.excluded); in := {}; out := {}
  for k, (ref, [s, g], I) in zip(body.inputs, header.inputs, W.inputs):
      Φp := W.children[ref.tx]                       or fail "no proof for parent"
      require well_formed_parcel(I.parcel) and ref.i < |Φp.outputs|
      require H("pcd-output", {ref, parcel: I.parcel}) == Φp.outputs[ref.i]   # input exists, validly
      require sigil(I.parcel) == s                                          # H("sigil", {home, lock, salt})
      p := I.parcel; σ := I.seal; C := I.charter
      require σ.sigil == s and σ.tid == W.tid and σ.gen == g and σ.constellation == p.home
      require C.version == σ.version and C.witnesses non-empty
      if C.version == 0: require H("constellation", C) == p.home            # later versions: holder checks hash
      counted := { v.witness : v in σ.votes, v.witness in C.witnesses, v.witness not in E,
                   Ed25519.verify(v.witness, "vote", {constellation, version, witness, sigil, gen, tid, time}, v.sig) }
      require |counted| >= q(|C.witnesses|)                                  # q(n) = n - floor((n-1)/3)
      rely(relied, p.home, C.version, H("charter", C), |counted| - q)        # keep min slack per (cid, version)
      require eval(p.lock, W.unlocks[s], s, W.tid, now = null)               # owner authorised; sigs over
                                                                             # {sigil, tid, expires}
      confirm(confirmed, p.home, confirmation_version(I.confirmation) or -1) # keep min version per cid
      in[p.asset] += p.amount

  # 5. conservation
  for o in body.outputs: require o.asset not in {"", "mint:"}; out[o.asset] += o.amount
  for each base asset X: require in[X] + in[mint:X] == out[X] + out[mint:X] and out[mint:X] <= in[mint:X]

  # 6. fold in the parents (each distinct parent once)
  for ptid in distinct(ref.tx for ref in body.inputs):
      Φp := W.children[ptid]
      verify(STEP_VK, digest(Φp))          # zkVM recursion syscall: the parent's proof exists
      for row in Φp.relied:    rely(relied, row...)        # min slack; same charter hash or fail
      for row in Φp.confirmed: confirm(confirmed, row...)  # min version
      if Φp.excluded != null: E := E ∩ Φp.excluded

  return {v, tid, outputs, relied: sorted(relied), excluded: sorted(E), confirmed: sorted(confirmed)}
```

`confirmation_version(c)`: `c.charter` is a charter body for `p.home` (version 0 must hash to the cid); at least *f*+1 distinct members of it have valid `attest` signatures over `{constellation, version, witness, sigil: s, gen: g, tid, time}`. Returns `c.charter.version`.

## Notes for the M1 port

* **Children are verified by digest.** `verify(STEP_VK, digest(Φp))` is `sp1_zkvm::lib::verify::verify_sp1_proof` in SP1 and `risc0_zkvm::guest::env::verify` in RISC Zero. Fan-in *k* costs *k* recursion verifications, paid by the proving system, not by guest cycles.
* **Version agility.** To let the guest change without stranding old proofs, accept `Φp.v ∈ ALLOWED_VKS` (a constant list compiled into the guest) and verify each child under its own `v`.
* **Cost** (measured in `research/rv32_cycles`, RV32IM, no precompiles): Ed25519 verification is 96–98 % of the instructions (≈ 3.3 M each). One input with 4 votes costs 17 M instructions, 5 inputs cost 84 M, one input with 31 votes costs 107 M. JSON parsing, canonical encoding and BLAKE2b (≈ 6.5 k instructions per 128-byte block) add up to under 3 %.
* **Encoding.** The reference hashes canonical JSON (sorted keys, no whitespace, ASCII). `serde_json` without `preserve_order` reproduces Python's `json.dumps(sort_keys=True, separators=(",", ":"))` on every test vector so far, but floats, non-ASCII and integer edge cases are not pinned. A v1 binary encoding removes that risk.
* **What stays outside the guest:** trust in constellations, charter-chain verification for versions > 0, the holder's conviction list and how fresh its deep confirmations must be. All of these are holder policy over `Φ` (see `HolderPolicy` in `research/pcd.py`).
