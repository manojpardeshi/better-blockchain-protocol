# Verification status

This document states precisely what has been **mathematically verified** about
Sigil, with which tool, under which assumptions, and — just as importantly —
what has **not**. "Safe and bug-free" is not a property any tool can establish
for a whole system; what follows is the honest decomposition.

Three kinds of evidence, in decreasing order of strength:

1. **Machine-checked proof, no size bounds** (TLAPS) — the core safety theorem,
   also under charter rotation and constellation succession.
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

### 1b. Safety under charter rotation, unbounded (`formal/SigilRotProofs.tla`)

`SigilRotProofs.tla` proves the same safety theorems **under charter rotation**,
for any number of charter versions (keys may be re-used across versions),
witnesses per version, sigils, transitions and generations: **3,467 proof
obligations, all checked by tlapm 1.6.0-pre with `--strict`**, none omitted.
Run it with `SIGIL_ROT_PROOF=1 formal/check.sh`, which also runs its TLC
instances (CI job `rotation-proof`); it takes tens of minutes, so the default
run skips both.

* `SpecSafety`: no sigil is an input of two different complete transitions.
* `SpecOneSealAcrossVersions`: at most one tid is sealed per (sigil, gen),
  counting the seals of every version.
* `SpecDeathProofsSound`: a death proof means the transition never completes.
* `SpecHonestNoEquiv`: an honest key, re-used or not, never signs two tids for
  one (sigil, gen), even across versions.

What is modelled, per honest key: it runs in one version at a time and only
moves forward; it may stay unfrozen in an old version (an ex-member that keeps
voting), FREEZE there, and ADOPT any later version it is a member of. Per sigil
it keeps the record of `sigil/witness.py` (gen, tid or NoTid or Contested,
candidates, abstain, the log of bind/release/seal entries) and performs SPEND,
RELEASE, the contested RELEASE, the seal-settled contested RELEASE (W9), FREEZE
and ADOPT with own-vote abstention. ADOPT reads the union of the snapshots of
the honest members of a freezing quorum of the previous version, plus what its
Byzantine members may add (bind entries for any transition, release entries
only with a valid death proof, seal entries only with a valid seal). Quorum
intersection between every seal or against-quorum of a version and every
freezing quorum of it is **proved**, not assumed. The ADOPT rule proved
(`LoneOK`, `ResolveOK`) is exactly the one in `sigil/witness.py` and the Rust
witness (§4, Bugs 3 and 4).

Assumptions: each version's charter is finite and non-empty with `q = n − f`,
`f = ⌊(n−1)/3⌋` and at most `f` Byzantine members (`VersionsFaultBounded`);
idealised cryptography (only `w` creates votes carrying `w`); one home
constellation whose charter chain is fixed (FREEZE binding one successor makes
it the only verifiable chain). Not modelled: holder validation, expiry and
time, the network, and wallets (see §2 and §3b for those).

The resource bounds (SPEC §5.1 step 2a and the generation cap, §5.2 step 1a, §5.6
admission control) leave the proof unchanged: each is a SPEND or RELEASE the witness
declines, and in the model SPEND and RELEASE are actions that may simply not be
taken, so every behaviour of the bounded witness is a behaviour of the spec. ADOPT
now keeps each distinct log entry once; the model's log and snapshots are already
sets (`lg`, `ld`, `sb`, `sd`), so the evidence ADOPT reads is the same set. The
proof was re-run after the change (`SIGIL_ROT_PROOF=1 formal/check.sh`).

TLC instances of the proved spec (`MC_rotp*.cfg`; `MC_rotp_cex.cfg`, the proved rule on
the Bugs 3/4 instance, is opt-in via `SIGIL_TLC_EXTRA` as it takes over 20 minutes) check that it is non-vacuous
(recovery after rotation, abstention, contested release, lone inheritance and
seal settlement are all reachable) and that each condition of the rule is
needed: removing the own-vote condition, the seal-settlement condition or the
`top <= g + 1` guard, or using the first sibling rule, is caught.

### 1c. Safety under constellation succession, unbounded (`formal/SigilSuccProofs.tla`)

`SigilSuccProofs.tla` proves the same safety theorems under rotation **and
constellation succession** (dead-man takeover, [SPEC §5.5](SPEC.md)), for any
number of charter versions, witnesses per version, successor-committee members,
sigils, transitions and generations, with keys re-used across versions and
committees: **4,208 proof obligations, all checked by tlapm 1.6.0-pre with
`--strict`**, none omitted, in about 16 minutes (970–994 s) from an empty
fingerprint cache on 4 cores; the whole `SIGIL_SUCC_PROOF=1 formal/check.sh`
run, with the base proof and the TLC instances, takes about 19 minutes.
Run it with `SIGIL_SUCC_PROOF=1 formal/check.sh` (CI job `succession-proof`),
which also runs its TLC instances.

* `SpecSafety`, `SpecOneSealAcrossVersions` (seals of every version count,
  those of a succeeded version included), `SpecDeathProofsSound` and
  `SpecHonestNoEquiv`, as in §1b.
* `OneSuccessor` / `OneSuccessorK`: the honest keys of a version (or of its
  committee) sign at most one successor each, so two different successors never
  both collect the authority's quorum, and the chain is the only one a holder
  can verify, whether its next version came from a rotation or a succession.

What is modelled, on top of §1b: every version may name a committee; MIRROR (an
unfenced honest standby member stores any owner-authorised binding; anyone may
push one); **mirror before vote** (an honest witness of a version with a
committee creates a vote only if a committee quorum's honest members stored the
binding); FENCE (a standby member signs a successor of its version and never
mirrors for it again); STANDBY (a committee enters standby with the evidence its
version's members adopt: a freezing quorum's snapshots, a fenced committee
quorum's mirror logs, or anything for version 0); and ADOPT after a succession
(from the mirror logs of a fenced committee quorum, plus anything its Byzantine
members add). Rotation stays available for every version, and old members are
never forced to stop: after a succession they keep voting (an old quorum that
was merely partitioned comes back), subject only to their own discipline. The
inductive invariant generalises the rotation proof's `Lineage` (the evidence any
key adopted for a version covers every earlier version, by a freezing quorum's
snapshots *or* a fenced committee quorum's mirror logs) and adds `MirVotes`
(behind every honest vote of a version with a committee there is a mirror
quorum), `StandbyLin` and `FenceShape`. Quorum intersection inside a committee
is proved (`HonestInBothKQuorums`), not assumed.

**Assumptions:** each version is fault-bounded as in §1b, and so is each
committee a version names (`q_k = n_k − f_k`, at most `f_k` Byzantine,
`CommitteesFaultBounded`); idealised cryptography; static corruption; and the
operator who drives a rotation or succession hands the new members and the new
committee the snapshots of the keys that signed (`_install` in
`sigil/network.py` and `sigil/server.py`), as for ADOPT in §1b. **No timing
assumption:** the dead-man period only decides when an honest standby member
fences, and FENCE may happen at any time in the model, so a partition mistaken
for death is covered. The heartbeat and dead-man machinery is liveness only.

**The proved rules match the code** (Python reference and Rust port alike): the
mirror-ack gate is checked when a vote is created and a refused SPEND stores
nothing; a standby member stands by for one version at a time, mirrors only
while unfenced, fences (durably) before it signs, and hands over its whole
mirror log. The resource bounds of standby members (an authorisation of at most
32 KiB, generations below 16, at most 4 transitions per sigil and generation,
release entries only for bindings it holds with death proofs of at most 128
KiB) are refusals of MIRROR, which the model allows not to happen, and the
STANDBY handover keeps the evidence as a set, as the model does.
`tests/test_succession_conformance.py` drives the real Python `Witness`,
`Standby` and `Network` under randomised adversarial schedules (an owner who
signs everything, a Byzantine witness, a Byzantine standby member in every
committee that acknowledges without storing, acks replayed across a
succession, old quorums coming back, crashes, rotations and takeovers) and
checks the model's `MirVotes`, the fence, inheritance, `HonestNoEquiv`,
`OneSealAcrossVersions` and `Safety` after every step: 25 × 45 steps by default
(182 votes, 24 takeovers, 41 rotations, 4 late votes by old quorums); 60 × 80
(539 votes, 76 takeovers, 85 rotations, 11 late votes) without violation. A
witness that ignores mirror acks, and a standby member that stores after it
fenced, are both caught. The Rust witness and standby member replay a 111-step
golden-vector script of the reference byte for byte (`succession` in
`rust/sigil-witness/tests/vectors.json`), and `bench/interop.py` runs a
dead-man takeover of a mixed Rust+Python home by a mixed committee.

TLC instances of the proved spec (`MC_succ*.cfg`, formal/README.md): instances A
(5,764 states) and C (three versions: a rotation into a version with a
committee, then its succession; 8,196 states) hold; removing mirror before vote,
the fence, the committee quorum of a succession, or the history a committee
must stand by with, is each caught; and probes show lone inheritance, contested
records, late votes by the old quorum, successor seals and recovery through a
succession are reachable. Instance B (`MC_succ.cfg`) is opt-in: it does not
finish within the CI budget.

The proof found one problem, in itself: the first complete draft stated four
frame steps as `\A E, v1 \in Vers : ...`, which TLA+ reads as bounding the
evidence `E` by `Vers` too, so nine obligations failed; quantifying `E`
unboundedly fixed them. No protocol or code bug was found by the succession
proof. Reviewing the code against the proved rules found one: the mirror-ack
gate failed open when a witness's registry lacked its own charter version (a
member of a version with a committee restarted with a registry file nobody
updated): it found no committee and voted without acks, which the model does
not allow. It now creates no vote until it knows its charter (Python and Rust,
`test_a_witness_without_its_own_charter_votes_on_nothing` and
`without_its_own_charter_nothing_is_voted_or_signed`).

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
| `MC_rot_sibling` | `MC_rot.tla` | the **implemented** ADOPT (`AdoptMode = "sibling"`, SPEC §5.4 / `witness.py`): same-generation siblings make the sigil contested; contested release | same | hold | 77,392 |
| `MC_rot_sibling4` | `MC_rot.tla` | as above, plus `Tg = {(s,1)}` (recovery spend at gen 1) | same + Tg | hold | 157,441 |
| `MC_rot_sibling_v1_mutant` | `MC_rot.tla` | the first sibling rule (`AdoptMode = "sibling_v1"`) on an instance where a sealed generation lies above a lone binding | Ty, Tb, Tu, Tg | **violated (expected)**, Bugs 3/4 | — |
| `MC_rot_sibling_top` | `MC_rot.tla` | the implemented rule (top of the evidence) on the same instance | Ty, Tb, Tu, Tg | opt-in (`SIGIL_TLC_EXTRA`): the state space exceeds the CI budget; `MC_rotp_cex` checks this instance in the proved spec, and `SigilRotProofs.tla` proves the rule for every instance | — |
| `MC_rot_sibling_witness`, `…_witness2`, `…_witness3` | `MC_rot.tla` | non-vacuity: Tg completes after rotation; a contested record is released; a contested record is settled by a seal | same + Tg | **violated (expected)** | — |
| `MC_expiry` | `SigilExpiry.tla` | **owner-signed expiry** + the wallet unpledge rule: with drifting clocks and arbitrarily delayed requests, once the wallet drops a pledge the tid can never be sealed | n=4 q=3, skew 1, `max_skew` 2, time 0..7 | hold | 113,030 |
| `MC_expiry_mutant`, `MC_expiry_skew_mutant` | `SigilExpiry.tla` | witness ignores expiry / wallet margin `max_skew < 2·skew` | same | **violated (expected)** | — |
| `MC_deep` | `SigilDeep.tla` | **deep confirmation** (SPEC §9): `f+1` current-charter confirmations ⇒ the binding is real, against a retired-key forgery; and the true binding is always confirmable | current n=4 f=1, threshold 2 | hold | 4 |
| `MC_deep_mutant` | `SigilDeep.tla` | threshold `f` instead of `f+1` | same | **violated (expected)** | — |
| `MC_wallet` | `SigilWallet.tla` | **the wallet state machine** composed with the witness protocol, with the proposed wallet fixes (§4b): (a) `NoSelfEquiv`, (b) `UnpledgeSound`/`AbortSound`, (c) `PaidIsComplete`/`HeldIsTracked`, (d) `OneComplete`, under delayed requests, seal failures, wallet crashes/restarts, a swap counter-party and a Byzantine witness | n=4 q=3 (1 Byz), 3 tids (1 swap), gens 0..1, TTL 2, time 0..5 + FOREVER | hold | 16,784 |
| `MC_wallet_live` | `SigilWallet.tla` | recovery liveness: a pledged tid that is provably dead is eventually abandoned (`WF` on Tick, Unpledge, Abort; no symmetry) | same, no crashes | hold | 53,456 |
| `MC_wallet_code` | `SigilWallet.tla` | the **current** code (payments only, as in the CLI; header dropped after a failed seal; abort needs a release quorum; `cmd_pay` save points): safety (a)(b)(c-paid)(d) | same, no swaps | hold | 2,203 |
| `MC_wallet_big` *(opt-in, ≈5 min)* | `SigilWallet.tla` | as `MC_wallet` | 4 tids (2 swaps), gens 0..2, time 0..6 | hold | 1,307,022 |
| `MC_wallet_gen_mutant` | `SigilWallet.tla` | **current** `authorise` (no generation check): reproduces wallet bug W4 | as `MC_wallet` | **violated (expected)** | — |
| `MC_wallet_pending_mutant` | `SigilWallet.tla` | **current** failed-seal handling (header forgotten): bug W6 | as `MC_wallet` | **violated (expected)** | — |
| `MC_wallet_abort_mutant` | `SigilWallet.tla` | **current** `abort` (needs a quorum of releases): bug W8, liveness | as `MC_wallet_live` | **violated (expected)** | — |
| `MC_wallet_crash_mutant` | `SigilWallet.tla` | library `Wallet.pay` (no save between authorise and the first request): bug W7 | as `MC_wallet` | **violated (expected)** | — |
| `MC_wallet_expiry_mutant`, `…_status_mutant`, `…_noproof_mutant` | `SigilWallet.tla` | unpledge without expiry / trusting one member's STATUS / abort without a death proof | as `MC_wallet` | **violated (expected)** | — |
| `MC_wallet_witness`, `…_witness2` | `SigilWallet.tla` | non-vacuity: a payment completes after an abort / after an expired pledge is dropped | as `MC_wallet` | **violated (expected)** | — |

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

What the wallet model covers (`formal/SigilWallet.tla`, SPEC §4, §5.1–5.2):
one parcel of an honest wallet whose home has 3 honest witnesses and 1
Byzantine one (votes for anything, always answers STATUS "unbound", claims
every release). Every authorisation the wallet ever signed stays deliverable
to any honest witness at any later time; honest witnesses newly bind only
before `expires`; anybody may release with a death proof. The wallet actions
mirror `Wallet.authorise`, a failing seal round, `finalise`,
`unpledge_if_unbound`, `abort` and a crash that restores the last
`wallet_store` save. A swap's counter-party writes the header (it may name any
generation for our sigil) and seals or kills its own leg at will. Flags select
the current code or the proposed fixes, so each wallet bug is a mutant that
TLC must reproduce. Abstractions: one global clock (the skew arithmetic is
`SigilExpiry.tla`'s job), one parcel, the counter-party's input as a
three-valued flag, no rotation, idealised cryptography, and the wallet's
honest construction of headers it builds itself. After `MAXT` the clock jumps
to `FOREVER` (later than every expiry, no new signatures), so liveness
counterexamples are not artefacts of the time bound.

TLC checks are **bounded**: they establish safety only up to the stated sizes.
The unbounded guarantees are the TLAPS proofs (§1, and §1b and §1c for rotation and succession).

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
does **not** verify the server, witness persistence, or the Rust witness.

## 3b. Wallet conformance (the real Python wallet)

`tests/test_wallet_conformance.py` drives the **real** `Wallet` (with
`wallet_store` restarts and `swap.propose_swap`) under randomised adversarial
schedules and checks the `SigilWallet.tla` invariants after every step. The
adversary: a Byzantine witness in the wallet's home (votes anything, lies
"unbound" in STATUS, claims releases); a link to the home that is good, lossy
(requests lost but delivered at a random later step, possibly after expiry;
replies lost; STATUS/RELEASE timeouts) or partitioned; wallet crashes in the
middle of sealing and restarts from disk at the `cmd_pay` save points; clock
jumps; retries of failed transitions; `abort` with death proofs; and a swap
counter-party who cooperates, double-spends her input first, splits her
witnesses or withholds her signature. Mapping: `pledge ← Wallet.pledged`,
`exp ← every expires the wallet signed` (a ghost that survives restarts),
`gen/bound/votes ← honest Witness.records` (+1 forged vote per Byzantine
member).

Checked: `NoSelfEquiv` at every signature (every other tid signed at that
`(s, g)` is already dead, or expired with too few votes to ever seal);
`UnpledgeSound`/`AbortSound` whenever a pledge disappears (dropped, replaced
or lost across a restart) and forever after; `OneComplete` and no double
finalise; `PaidIsComplete`; every **un-pledged** holding is unspent and
verifies from the wallet's own dossier with a fresh validator.

* **Result:** the real wallet satisfies them. Default 12 seeds × 40 steps
  (≈ 4 s: 50 transitions signed, 33 finalised, 17 failed seals, 8 pledges
  dropped, 53 restarts); 80 × 80 (`SIGIL_WALLET_SEEDS`/`SIGIL_WALLET_STEPS`,
  ≈ 70 s): 460 signed, 292 finalised, 168 failed seals, 56 drops, 14
  legitimate re-pledges of one `(s, g)`, 640 restarts, no violation.
* **Mutation tests:** a wallet that drops unexpired pledges, and one whose
  `authorise` forgets earlier pledges, are both caught.
* **Restrictions** (each is a known bug with its own test, §4b): the
  harness does not assert `HeldIsTracked`/`RecoveryLive` (W6, W8), does not
  re-authorise a stale-generation header (W4 — the run found this path
  itself), and does not attack with crafted headers, poisoned dossiers or
  rogue constellations (W1–W5, tested directly).

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

### Bugs 3 and 4 — ADOPT re-opened higher generations (found by the unbounded proof)

Found while proving rotation safety for unbounded versions
(`formal/SigilRotProofs.tla`, work in progress), and fixed. Both come from the
first version of the Bug 1 fix, which inherited a lone live binding `(g, t)`
whenever nothing else was bound **at** `g`, and forgot that the evidence, or the
adopter's own votes, already reached a **higher** generation. A later release
then moved the record to `g + 1` only.

* **Bug 3 (double spend).** `Tu` is sealed at `(s, 1)` and later released
  (another input of it is consumed), while `Tb` stays bound at `(s, 0)`. ADOPT
  inherited `Tb` at 0; once `Tb` died, the new charter sealed a second
  transition at `(s, 1)`.
* **Bug 4 (an honest re-used key framed).** A key that voted at `(s, 1)` and
  missed the FREEZE inherited a lone binding at 0, and after its release voted
  a different transition at `(s, 1)`: a valid SPEC §3.8 equivocation proof
  against an honest witness.

**Fixed** (SPEC §5.4, Python and Rust): a lone live binding is inherited only on
top of the evidence (every other binding below `g`, or at most `g` with a valid
seal for it) and when the key's own votes are at most `g`; otherwise the record
is contested, and the contested release moves past every candidate and the
key's own votes. A seal settles a contested record only under the same vote
condition. Reproduced in `tests/test_conformance.py` `RotationOpenBugTests`
(now regression tests), in the golden vectors (`rotation_top`, replayed by the
Rust witness), and at the model level by `formal/MC_rot_sibling_v1_mutant.cfg`
(the first rule, violated); `MC_rot_sibling_top.cfg` checks the fixed rule on
that instance. The bounded configs missed it because their instances had one
transition per higher generation and no re-used honest key.

### Not a bug, now covered

The seal-field override reported by the Rust golden-vector work
(`votes_of_seal` let an entry override the seal's own fields) was fixed upstream
in commit `f14a533` and merged into this branch; the TLAPS proof and all TLC
models assume the fixed semantics (a vote is counted only under the seal's own
`(constellation, version, sigil, gen, tid)`).

---

## 4b. Wallet bugs found (all fixed)

All ten are fixed in `sigil/wallet.py`, `sigil/wallet_store.py`,
`sigil/validate.py` (`Dossier.merge`), `sigil/cli.py` and, for W9,
`sigil/witness.py`. The twelve reproductions in `tests/test_wallet_findings.py`
were expected failures, each shown to fail by assertion against the old code;
they now run as regression tests. TLA⁺ mutants reproduce W4, W6, W7 and W8 at
the model level, and the fixed design is model-checked (`MC_wallet`,
`MC_wallet_live`). Fixes, in brief:

* **W1, W2.** A wallet's default trust is its home plus the constellations its
  network was configured with at creation; charters a dossier introduces are
  learned but never trusted unless the owner calls `Wallet.trust`. The policy
  (`trusted`, convicted witnesses) is saved and restored, and a saved policy of
  "trust anything" is refused on load.
* **W3.** `receive` merges only the verified ancestry, and `Dossier.merge`
  never replaces an entry it holds (charters only by extension, never a fork).
* **W3b, W10.** `receive` accepts only addresses the wallet issued (exact
  sigil), and never a second parcel with a sigil it already holds.
* **W4, W5.** `authorise` checks the header commits to the body, that the
  input lists line up, that each own input has its own sigil and current
  generation, and refuses while any live pledge of the sigil names another tid.
* **W6, W7.** Authorised transitions are kept as `pending` (saved with the
  pledge); an `on_pledge` hook saves the wallet before any witness sees an
  authorisation (the CLI uses it). After expiry, `release_expired_pledges`
  drops a pledge that bound nothing, or completes the transition with a fresh
  authorisation of the same tid, or aborts it. `authorise` also refuses when a
  member reports a binding or vote at that generation for a tid it has no
  pledge for (a pledge lost in a crash).
* **W8.** `abort` frees the inputs at `g + 1` as soon as a death proof
  verifies (SPEC §4 rule 2 now says so), releasing every witness still bound.
* **W9.** RELEASE of a CONTESTED record also accepts a valid seal for its one
  remaining candidate and binds to it (SPEC §5.2); the seal is logged so a
  later ADOPT inherits the binding. `deep_confirm` shows such a seal from the
  dossier to any current member that reports the sigil contested. Model-checked
  as `ResolveContested` in `formal/SigilRot.tla` (`MC_rot_sibling*`, with
  non-vacuity config `MC_rot_sibling_witness3`).

| # | Severity | Where | Bug | Impact | Test |
|---|---|---|---|---|---|
| W1 | critical | `wallet_store.load` | the trust policy (`trusted`) is not persisted; a reloaded wallet trusts every charter in the registry, and `verify_parcel` adds any chain a dossier carries | counterfeit: one parcel moved to an attacker's one-witness constellation is "spent" to any number of victims | `TrustPolicyTests.test_restarted_wallet_keeps_its_trust_policy` |
| W2 | critical | `cli cmd_init` | CLI wallets are created with no trust policy at all | as W1, for every CLI wallet | `TrustPolicyTests.test_cli_wallet_does_not_trust_constellations_named_by_a_payer` |
| W3 | high | `Wallet.receive` → `Dossier.merge` | every entry of a received dossier, verified or not, overwrites the wallet's own transitions and seals | any payer can make the wallet's own coins unprovable: its next payments are consumed but rejected by recipients | `DossierIntegrityTests` |
| W3b | high | `Wallet.receive` | a parcel is accepted if its lock merely *mentions* one of our keys (`any(sig(us), sig(payer))`) | the payer claws the payment back; `balance` counts it | `ReceiveLockTests.test_receive_rejects_a_parcel_the_payer_can_still_spend` |
| W4 | high | `Wallet.authorise` | no check that the header's generation (and sigil) for our input matches the holding; the equivocation guard only covers a pledge at the *same* generation and otherwise overwrites it | a counter-party's header (or the wallet's own stale header after `abort`) makes the wallet sign two tids for one `(s, g)` — SPEC §4 rules 1–2 | `AuthoriseTests.test_authorise_refuses_a_header_at_another_generation`, `MC_wallet_gen_mutant` |
| W5 | high | `Wallet.authorise` / `swap` | no check that `header.body = H(body)` | swap: the counter-party shows a body that pays us and gets our signature on one that does not — paid-without-being-paid (f) | `AuthoriseTests.test_authorise_checks_the_header_commits_to_the_body` |
| W6 | high | `Wallet.transact`, `cli cmd_pay`, `wallet_store` | after `SealFailed` (or a crash mid-seal) the header and body are dropped and never persisted | an input bound at a minority is frozen forever while `balance` shows it; a later-completed payment is lost to both sides | `PendingTransitionTests.test_failed_payment_does_not_freeze_its_input`, `…test_cli_restart_mid_seal_can_finish_the_payment`, `MC_wallet_pending_mutant` |
| W7 | medium | `Wallet.pay`/`transact` (library) | no point to persist the pledge between `authorise` and the first request | a crash, then a restart from the last save, signs a second tid at `(s, g)` | `PendingTransitionTests.test_library_pay_cannot_lose_a_pledge_in_a_crash`, `MC_wallet_crash_mutant` |
| W8 | medium | `Wallet.abort` | drops the pledge only if a quorum *released*; never-bound witnesses do not count, and `unpledge` is then blocked by the released witnesses' vote history | a betrayed swap input bound at fewer than q witnesses is frozen forever (one crash + one silent Byzantine suffice) | `AbortTests`, `MC_wallet_abort_mutant` (liveness) |
| W9 | medium | wallet × witness ADOPT | a pledge legitimately released under SPEC §4 rule 3 plus one Byzantine witness's genuine (expired) bind in its FREEZE evidence makes the sigil CONTESTED after rotation, forever | deep confirmation of the legitimate payment fails forever (or the sigil is frozen if the rotation came first) | `RotationFindings` |
| W10 | low | `Wallet.receive` | two parcels paid to one address share a sigil; both are credited | `balance` overstates; only one is spendable | `ReceiveLockTests.test_two_parcels_on_one_sigil_are_not_both_credited` |

Also noted: `wallet_store.load` dropped `pledge_ttl` and `max_skew` (now
saved); `finalise` never deletes the pledges of consumed inputs (harmless);
`unpledge_if_unbound` counts answering *witness objects* against the charter
size, so a directory listing one member twice would let it skip a member
(`MC_wallet_status_mutant` shows why every member must answer); and STATUS
answers are unauthenticated, so both rule-3 releases and deep confirmation
are only as strong as the transport.

**What holds (properties (a)–(f)).** With honest header construction:
(a) no self-equivocation and (b) pledges released only when unsealable hold
for the current code under crashes, delays, expiry and a Byzantine witness
(`MC_wallet_code`, conformance); W4 and W7 break (a) under a hostile header
or library use without a save point. (c) Reported payments are complete
(holds); holdings are *not* reliable (W1–W3b, W6, W10). (d) Recovery never
double-spends (holds: `OneComplete`, `AbortSound`), but can fail to recover
(W8). (e) `deep_confirm` requires `f + 1` members of the **current** charter
reporting `(gen, tid)`, as SPEC §9 says (code inspection, `MC_deep`,
`tests/test_deep_confirmation.py`), with the transport and W9 caveats above.
(f) Atomicity holds at the transition level (a transition is valid only if
every input is sealed), but W5 lets a counter-party substitute the body; and
two protocol-level gaps remain (below).

## 5. What is **not** verified (the honest gaps)

The results above concern the **witness protocol and its abstract model** under
**idealised cryptography**. None of the following is verified:

* **Rotation and succession are proved, but on abstract models.**
  `SigilRotProofs.tla` and `SigilSuccProofs.tla` prove safety for unbounded
  versions and sizes (§1b, §1c); the code is linked to them by conformance
  tests and golden vectors, not by a proof of the code itself. The liveness of
  succession (SPEC §5.5 L1–L3: the committee gates progress, no premature
  takeover under the stated timing, recovery after death) is argued, tested
  (`tests/test_succession.py`, `bench/interop.py`) and not proved.
* **Wallet logic** is now model-checked on small instances (one parcel,
  ≤ 4 transitions, generations ≤ 2, `SigilWallet.tla`) and conformance-tested
  (§3b) — not proved for all sizes, and not composed with rotation (W9 was
  found by a targeted test, not by a model). `select`/change computation,
  `issue`/`mint`, stamps, the HTTP `RemoteNetwork` and multi-parcel
  bookkeeping are only covered by the existing unit tests.
* **Swaps between two processes.** `swap.atomic_swap` runs both parties in one
  process. A real exchange also needs: checking exactly which of our inputs a
  proposed body consumes and that our change comes back (`_pays` checks only
  that we are paid); getting the counter-party's unlocks *before* releasing
  ours (otherwise a completed swap can be withheld: without them we cannot
  build a valid dossier for our output); and a way out when the counter-party
  never seals nor spends its own input — our sealed input is then held
  hostage indefinitely (fair exchange; no death proof ever exists). None of
  this is specified or implemented.
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
* **The Rust witness and standby member** (`rust/`): checked only against the
  Python reference by golden vectors and interop runs in their own CI job, not
  against the formal model.
* **Liveness / availability**: only *safety* is addressed. Nothing here proves
  the protocol makes progress, resists censorship, or recovers funds in bounded
  time.
* **Bounds are bounds**: the TLC results hold only up to the instance sizes in
  the table; only the TLAPS theorems (§1, §1b, §1c) are size-free, and they
  are about abstract models of the witness and standby protocols.

"Bug-free" is therefore **not** claimed for any code. What is established is: the
single-version witness protocol's core safety theorem holds for all sizes under
the stated assumptions (machine-checked); several rotation/expiry/confirmation
properties hold on small instances (machine-checked, with mutation tests); the
real witness code refines the proved model on non-rotation schedules (tested);
two concrete safety-relevant bugs in the reference witness were found,
reproduced and fixed, with the fixed ADOPT model-checked; and the wallet's
pledge discipline is model-checked and conformance-tested, with ten open
wallet bugs reproduced (§4b).

---

## 6. Reproducing

```sh
# TLAPS unbounded proof + all bounded TLC models with mutation tests (~8 min):
formal/check.sh
# + the rotation proof and its instances (~40 min), the succession proof and its instances (~20 min):
SIGIL_ROT_PROOF=1 formal/check.sh
SIGIL_SUCC_PROOF=1 formal/check.sh
# just the proof:
formal/check.sh            # (TLAPS runs only with no config args)
SIGIL_SKIP_TLAPS=1 formal/check.sh MC_rot.cfg MC_rot_mutant.cfg   # one TLC pair
SIGIL_TLC_EXTRA=MC_proofs.cfg formal/check.sh                    # + the 5-min non-vacuity run
SIGIL_SKIP_TLAPS=1 formal/check.sh MC_wallet.cfg MC_wallet_gen_mutant.cfg   # wallet model + a bug
SIGIL_TLC_EXTRA=MC_wallet_big.cfg formal/check.sh                # + the 5-min larger wallet instance

# conformance of the real witness, and the rotation regression tests:
python -m unittest tests.test_conformance
# succession: conformance of the real Witness/Standby/Network, unit and adversarial tests
python -m unittest tests.test_succession_conformance tests.test_succession tests.test_succession_wire
SIGIL_SUCC_SEEDS=60 SIGIL_SUCC_STEPS=80 python -m unittest tests.test_succession_conformance
SIGIL_CONFORMANCE_SEEDS=120 SIGIL_CONFORMANCE_STEPS=150 \
    python -m unittest tests.test_conformance.ConformanceTests

# the wallet: conformance of the real Wallet, and the open bugs (expected failures)
python -m unittest tests.test_wallet_conformance tests.test_wallet_findings
SIGIL_WALLET_SEEDS=80 SIGIL_WALLET_STEPS=80 python -m unittest tests.test_wallet_conformance
```

Tooling: TLAPS (tlapm 1.6.0-pre, bundling Zenon/Z3/Isabelle) and TLC
(tla2tools 1.7.4), both downloaded on first use into `~/.cache/sigil-tla`,
pinned and SHA-256-verified, over TLS. Linux x86_64 for the proof; TLC needs
only Java ≥ 11.
