# Verification status

This document states precisely what has been **mathematically verified** about
Sigil, with which tool, under which assumptions, and — just as importantly —
what has **not**. "Safe and bug-free" is not a property any tool can establish
for a whole system; what follows is the honest decomposition.

Three kinds of evidence, in decreasing order of strength:

1. **Machine-checked proof, no size bounds** (TLAPS) — the core safety theorem.
2. **Exhaustive bounded model checking** (TLC) — features the proof abstracts
   away, on small instances, each with mutation tests that must fail.
3. **Randomised conformance testing** — the real Python `Witness` is checked,
   step by step, against the abstract model the proof is about.

Everything here is reproducible with `formal/check.sh` (TLAPS proof + TLC
models) and `python -m unittest tests.test_conformance` (conformance + rotation
regression tests). The tools download pinned, SHA-256-checked binaries over TLS.

---

## 1. What is proven with no size bounds (TLAPS)

`formal/SigilProofs.tla` is an abstract transition system faithful to the
witness protocol of [SPEC §5.1–§5.2](SPEC.md) and the death proofs of §3.9, with
a single charter version per constellation. TLAPS (the TLA⁺ Proof System,
backends Zenon, Z3 4.8.9 and Isabelle2025) machine-checks the following for
**arbitrary** numbers of witnesses, sigils, transitions, generations and
constellations — there is no `MaxGen`, no bound on the sets, no enumeration.

| Theorem (module `SigilProofs`) | Statement | Status |
|---|---|---|
| `SpecSafety` | `Spec ⇒ □Safety`: in every reachable state, no sigil is an input of two different *complete* transitions (SPEC §8 Theorem) | **proved** |
| `SpecOneSealPerGen` | `Spec ⇒ □OneSealPerGen`: for any `(sigil, gen)` and charter version, at most one tid has a valid seal (SPEC §8 Lemma 1) | **proved** |
| `SpecDeathProofsSound` | `Spec ⇒ □DeathProofsSound`: a transition with a valid death proof is never complete, *including* the home-constellation binding of §3.9 (SPEC §8 Lemma 2) | **proved** |
| `SpecHonestNoEquiv` | `Spec ⇒ □HonestNoEquiv`: an honest witness never signs two tids for one `(constellation, sigil, gen)` | **proved** |

The proof is by an inductive invariant `Inv` (`InitInv`, `NextInv`, and
`Inv ⇒ Safety`), discharged through **842 proof obligations, all checked** in
≈ 60 s (`check.sh` runs it with `--strict`, i.e. incomplete proofs are errors).

**Quorum intersection with Byzantine witnesses is proved, not assumed.** Lemma
`HonestInBothQuorums` shows any two quorum-sized subsets of a fault-bounded
constellation share an *honest* member. It rests only on the finite-set
cardinality theorems of the TLAPS standard library (`FS_Union`, `FS_Subset`,
`FS_Difference`, `FS_Intersection`, `FS_MajoritiesIntersect`, `FS_CardinalityType`),
which are themselves machine-checked in that library and are the **only**
mathematical facts taken as given. The arithmetic fact `n > 3f` (where
`f = ⌊(n−1)/3⌋`) is discharged by Z3 (`FaultArith`).

### Assumptions of the proof (hypotheses, stated as `ASSUME`)

* Every constellation's membership is a **finite, non-empty** set.
* Every sigil's **home** satisfies the fault bound: `q = n − f` with
  `f = ⌊(n−1)/3⌋`, and **at most `f` Byzantine** members (SPEC §8). Other
  constellations (e.g. attacker-run "rogue" ones) are unconstrained but home no
  sigil of the model — a holder that trusts a rogue home has no guarantee, by
  assumption.
* Cryptography is **idealised**: a vote is a record, and only witness `w` can
  create a vote carrying `wit ↦ w`. Hashes, Ed25519 and tids are opaque
  identifiers; the sigil→home commitment of §3.2 is the constant map `Home`.
* The owner is **fully adversarial** (every spend request may reach any honest
  witness, in any order, at any time), and Byzantine witnesses may sign any
  vote for themselves. Votes are public and never disappear (STATUS, §5.3).

### What the proof abstracts away (hence does **not** cover)

Charter rotation (FREEZE/ADOPT, multiple versions, the contested state);
holder-side validation (conservation, output well-formedness); owner-signed
expiry; stamps; wall-clock time; the network; and bounded generations. These
are covered — to a bounded extent — by §2 and §3 below, or listed as gaps in §4.

A second TLA⁺ model, `formal/Sigil.tla`, is the pre-existing *concrete* model
that TLC checks exhaustively on fixed small instances (including a rogue
all-Byzantine constellation). It and `SigilProofs.tla` describe the same
transition system; `MC_proofs.cfg` (below) cross-checks that the proof's own
module is non-vacuous and that its invariant holds on reachable states.

---

## 2. What is model-checked exhaustively (TLC)

Each model is checked on a small instance; `*mutant*` / `*witness*` configs
**must** report a violation (so we know the checks have teeth). State counts are
from TLC 1.8.0 on 4 cores. All of these run from `formal/check.sh`.

| Config(s) | Module | What it checks | Bound / instance | Result | Distinct states |
|---|---|---|---|---|---|
| `MC`, `MC_all`, `MC_lazy` | `Sigil.tla` | SPEC §8 on the concrete witness model, 1 constellation | n=4 q=3, gens 0..2, all headers / eager+lazy Byz | hold | 47k / 688k / 517k |
| `MC_multi`, `MC_multi_all` | `Sigil.tla` | §8 across several constellations incl. a rogue one | C=4,D=1,R=1 | hold | 3.7k / 60k |
| `MC_mutant`, `MC_multi_mutant` | `Sigil.tla` | death proof accepted with no proof / from any constellation | — | **violated (expected)** | — |
| `MC_proofs_witness`, `MC_proofs_witness2` | `MC_proofs.tla` | non-vacuity: the proof's own spec reaches completions and releases | n=4, 2 sigils, 3 tids, gens 0..1 | **violated (expected)** | — |
| `MC_proofs` *(opt-in, ≈5 min)* | `MC_proofs.tla` | the proved invariant and §8 hold on all reachable states of a concrete instance; every `ASSUME` is evaluated | same | hold | **774,144** |
| `MC_rot` | `MC_rot.tla` | **charter rotation**: Safety, cross-version Lemma 1 (`OneSealAcrossVersions`) and honest non-equivocation across FREEZE/ADOPT, with the *fixed* ADOPT | 2 versions of C (n=4 q=3 each), sigils s,x, gens 0..1, eager Byz | hold | 44,746 (depth 19) |
| `MC_rot_mutant` | `MC_rot.tla` | the **old** ADOPT (before the Bug 1 fix) | same | **violated (expected)** — reproduces the double-spend of §4, Bug 1 | ~4k (depth 10) |
| `MC_rot_sibling` | `MC_rot.tla` | the **implemented** ADOPT (`AdoptMode = "sibling"`, SPEC §5.4 / `witness.py`): same-generation siblings make the sigil contested; contested release | same | hold | 11,916 |
| `MC_rot_sibling4` | `MC_rot.tla` | as above, plus `Tg = {(s,1)}` (recovery spend at gen 1) | same + Tg | hold | ~28k |
| `MC_rot_sibling_witness`, `…_witness2` | `MC_rot.tla` | non-vacuity: Tg completes after rotation; a contested record is released | same + Tg | **violated (expected)** | — |
| `MC_expiry` | `SigilExpiry.tla` | **owner-signed expiry** + the wallet unpledge rule: with drifting clocks and arbitrarily delayed requests, once the wallet drops a pledge the tid can never be sealed | n=4 q=3, skew 1, `max_skew` 2, time 0..7 | hold | 113,030 |
| `MC_expiry_mutant`, `MC_expiry_skew_mutant` | `SigilExpiry.tla` | witness ignores expiry / wallet margin `max_skew < 2·skew` | same | **violated (expected)** | — |
| `MC_deep` | `SigilDeep.tla` | **deep confirmation** (SPEC §9): `f+1` current-charter confirmations ⇒ the binding is real, against a retired-key forgery; and the true binding is always confirmable | current n=4 f=1, threshold 2 | hold | 4 |
| `MC_deep_mutant` | `SigilDeep.tla` | threshold `f` instead of `f+1` | same | **violated (expected)** | — |

What the rotation model covers (SPEC §5.4): FREEZE then ADOPT over two charter
versions with evidence logs (bind/release entries), the **contested** state,
**own-vote abstention** semantics, a **re-used** (Byzantine) key, **unfrozen**
ex-members (generation jumps), and **cross-version seals** (holders accept a
seal from any version, §6.4). Byzantine votes are *eager* — every vote the
Byzantine key could sign exists from the start — which is the standard sound
over-approximation (the `Spend` guard never reads votes; `Release` and `Sealed`
are monotone in votes), and it also keeps the state space tractable. The
adversarial *forged-snapshot* dimension of rotation (a lying predecessor
handing new members fabricated logs) is exercised by the pre-existing Python
explorer `tests/test_model_check_extended.py`, not re-modelled here.

TLC checks are **bounded**: they establish safety only up to the stated sizes.
The unbounded guarantee is the TLAPS proof (§1), which does not cover rotation.

---

## 3. Code-to-model conformance (the real Python witness)

`tests/test_conformance.py` closes the gap between the abstract model and the
executable `sigil.witness.Witness`. It drives the **real** witness under
randomised adversarial schedules (equivocating owner, a Byzantine witness,
well-formed and malformed spends, releases with assembled death proofs, status
queries) and, after **every step**, checks that the witness's state and the
votes it emits are allowed by the abstract model of `SigilProofs.tla`.

**Refinement mapping** (documented in the test):

```
abstract gen[w][s]    ←  w.records[s].gen          (0 when absent)
abstract bound[w][s]  ←  w.records[s].tid           (NoTid ← None)
abstract votes        ←  every (constellation, witness, sigil, gen, tid) in w.records[s].votes
```

Checked after each step: the abstract `Spend` precondition (an honest witness
emits a vote for `(s,g,t)` only when, just before, `g = gen` and `tid ∈ {⊥,t}`,
or `g > gen` and `tid = ⊥`); `HonestNoEquiv`; `VoteBelowGen`; `BoundVote`;
generation monotonicity; that malformed requests are refused without mutating
state or leaking exceptions; and, over the whole network, SPEC §8 (`OneSealPerGen`
and no double consumption). A mutated "amnesiac" witness that forgets its
generation floor is caught, so the checks are not vacuous.

* **Result (no rotation): the real witness conforms.** Default run (40 seeds ×
  60 steps) ≈ 3 s; scales via `SIGIL_CONFORMANCE_SEEDS` / `SIGIL_CONFORMANCE_STEPS`
  (120 × 150 ≈ 25 s) with no violation.
* **With rotation**, conformance against the single-version model does not apply;
  `RotationRegressionTests` covers the two rotation bugs of §4.

This links the verified model to the code for the single-version witness. It
does **not** verify the wallet, the server, persistence, or the Rust witness.

---

## 4. Bugs found

Both are **fixed** in `sigil/witness.py`, and `tests/test_conformance.py`
(class `RotationRegressionTests`) now holds them as regression tests: each
fails against the old code and passes with the fix. The ADOPT test also covers
the dual scenario below, and fails against the naive one-line patch.

### Bug 1 — ADOPT re-opens a consumed generation (safety: double-spend)

`sigil/witness.py :: Witness.adopt`. When the owner equivocates at one
generation and the **sealed** sibling is later proven dead while an **unsealed**
sibling stays "alive", ADOPT re-binds the unsealed sibling after rotation and
the new charter seals it — a **second seal for one `(sigil, gen)`** and a double
consumption. Reproduced against the real code (all witnesses honest; only the
owner misbehaves; standard `Network.rotate`) and, at the model level, by
`formal/MC_rot_mutant.cfg`.

This is **not a shallow logic slip**: ADOPT decides from `(binds, dead)` — the
set of bindings made and the set of tids proven dead. Two scenarios produce the
**identical** `binds = {(0,Tb),(0,Ta)}, dead = {Tb}` but require **opposite**
safe outcomes:

* *Tb sealed, Ta unsealed, Tb dead* → gen 0 already yielded a seal (Tb) that is
  now dead; it must be **closed**, Ta must not be resurrected. (The double-spend.)
* *Ta sealed, Tb unsealed, Tb dead* → the live seal at gen 0 is Ta; it must be
  **kept**. (`scratchpad` repro `repro_dual.py`; the real code is correct here.)

Since the inputs are identical but the correct outputs differ, **no function of
`(binds, dead)` can be correct** — ADOPT is information-insufficient. A naïve
"drop alive bindings below the floor" patch is therefore wrong (it breaks the
second scenario; `MC_rot` found this).

**Implemented fix.** ADOPT inherits a lone alive binding only if no other tid
was bound at its generation. Otherwise the sigil becomes **contested** with the
alive bindings as candidates, and RELEASE removes each candidate once it is
proven dead (SPEC §5.2, §5.4). This needs no seals in the evidence. A sealed
binding is always in the evidence (quorum intersection), so with siblings at its
generation the new charter never votes there: it waits until every live
candidate is dead. In both scenarios above this is safe: in the first, Tb's seal
proves Ta dead and the owner recovers at generation 1; in the second, nothing
proves Ta dead and s stays consumed by Ta. The cost is liveness for an owner who
equivocated: an unsealed sibling that can never be proven dead keeps the sigil
contested. `formal/MC_rot_sibling*.cfg` checks the rule (`AdoptMode =
"sibling"`); the idealised seal-aware ADOPT below is kept as `MC_rot.cfg`.

**Idealised alternative (verified safe in the model).** ADOPT could key off the **seals**
that formed in the old version, not the raw bindings: the record for `(s,g)` is
whatever tid a quorum *sealed* there (SPEC §8 Lemma 1 ⇒ at most one), advanced
if that tid is dead; an unsealed bind is a mere attempt and is ignored. This
requires FREEZE evidence to carry the seals (or `q` votes per sealed
`(sigil, gen)`), which the current evidence log does not. With this
"seal-aware" ADOPT, `formal/MC_rot.cfg` holds exhaustively (44,746 states);
with the current ADOPT, `MC_rot_mutant.cfg` finds the double-spend. The SPEC §8
"Rotation" paragraph has the matching gap: it argues that *sealed* bindings
carry over, but not what happens to an *unsealed* sibling of a sealed-then-dead
binding at the same generation.

### Bug 2 — FREEZE signs multiple conflicting successor charters (charter fork)

`sigil/witness.py :: Witness.freeze`. A frozen witness will sign **any number**
of different successor charters: it checks only `next_charter.prev` and the
`frozen` flag, never that it already committed to a different successor. So
every honest witness can be made to sign two version-(v+1) charters with
disjoint membership, each reaching a quorum of v and each passing
`charter.verify_chain` — a **charter fork**. A victim that adopts the attacker's
fork has its "current charter" — the one SPEC §9 deep confirmation trusts —
populated with attacker keys, which defeats deep confirmation (an honest witness
was tricked into certifying the attacker's successor). SPEC §3.7 ("v+1 MUST be
signed by a quorum of v") and the whitepaper ("a quorum signs *the* new
charter") both intend a single successor.

**Fixed.** FREEZE binds to one successor: it persists the frozen successor's
`charter_hash` and refuses a later `freeze` of a different `next_charter`
(the same one is signed again). Stores written before the fix hold `true`, so
their successor is unknown and any second freeze is refused. *(Confidence: the double-signing is certainly unintended;
end-to-end exploitation additionally needs the victim to adopt the attacker's
fork, which `verify_chain` currently accepts.)*

### Not a bug, now covered

The seal-field override reported by the Rust golden-vector work
(`votes_of_seal` let an entry override the seal's own fields) was fixed upstream
in commit `f14a533` and merged into this branch; the TLAPS proof and all TLC
models assume the fixed semantics (a vote is counted only under the seal's own
`(constellation, version, sigil, gen, tid)`).

---

## 5. What is **not** verified (the honest gaps)

The results above concern the **witness protocol and its abstract model** under
**idealised cryptography**. None of the following is verified:

* **Rotation is only bounded-checked.** The proof covers a single charter
  version. The implemented ADOPT is model-checked for two versions, two
  sigils, up to four transitions and generations 0..1, with the freezing
  quorum's logs modelled as the full honest union.
* **Wallet logic** (`sigil/wallet.py`): selection, authorisation, pledge
  bookkeeping, deep-confirmation orchestration, abort/recovery. Only the
  witness-facing *expiry* and *deep-confirmation counting* rules are modelled
  (§2), as pure arithmetic over idealised answers — not the wallet code.
* **Cryptographic primitives**: BLAKE2b, Ed25519, RSA-FDH stamps, and canonical
  JSON encoding are assumed collision-free / unforgeable / unambiguous. The
  proof replaces them with opaque identifiers. (`mypy` on the core modules
  surfaces only `Optional`-narrowing noise, no new finding.)
* **Persistence / durability** (`sigil/store.py`): the SPEC §5 "durable before
  you answer" requirement is inspected by hand, not model-checked; crash/restart
  interleavings and SQLite semantics are not verified.
* **Networking, the server, concurrency** (`sigil/server.py`, `sigil/gossip.py`,
  `witnessd.py`, the testnet): out of scope. The models deliver messages
  atomically as honest-witness actions.
* **The Rust witness** (`rust/`): checked only against the Python reference by
  golden vectors in its own CI job, not against the formal model.
* **Liveness / availability**: only *safety* is addressed. Nothing here proves
  the protocol makes progress, resists censorship, or recovers funds in bounded
  time.
* **Bounds are bounds**: the TLC results hold only up to the instance sizes in
  the table; only the TLAPS theorem (§1) is size-free, and only for the
  single-version witness.

"Bug-free" is therefore **not** claimed for any code. What is established is: the
single-version witness protocol's core safety theorem holds for all sizes under
the stated assumptions (machine-checked); several rotation/expiry/confirmation
properties hold on small instances (machine-checked, with mutation tests); the
real witness code refines the proved model on non-rotation schedules (tested);
and two concrete safety-relevant bugs in the reference code were found,
reproduced and fixed, with the fixed ADOPT model-checked.

---

## 6. Reproducing

```sh
# TLAPS unbounded proof + all bounded TLC models with mutation tests (~8 min):
formal/check.sh
# just the proof:
formal/check.sh            # (TLAPS runs only with no config args)
SIGIL_SKIP_TLAPS=1 formal/check.sh MC_rot.cfg MC_rot_mutant.cfg   # one TLC pair
SIGIL_TLC_EXTRA=MC_proofs.cfg formal/check.sh                    # + the 5-min non-vacuity run

# conformance of the real witness, and the rotation regression tests:
python -m unittest tests.test_conformance
SIGIL_CONFORMANCE_SEEDS=120 SIGIL_CONFORMANCE_STEPS=150 \
    python -m unittest tests.test_conformance.ConformanceTests
```

Tooling: TLAPS (tlapm 1.6.0-pre, bundling Zenon/Z3/Isabelle) and TLC
(tla2tools 1.8.0), both downloaded on first use into `~/.cache/sigil-tla`,
pinned and SHA-256-verified, over TLS. Linux x86_64 for the proof; TLC needs
only Java ≥ 11.
