# Verifying the Rust witness

This document records what is machine-checked about the Rust witness
(`rust/sigil-witness`), what is only tested, the bugs found, and what could not be done.
It complements [VERIFICATION.md](VERIFICATION.md), which covers the protocol model and
the Python reference. Everything here can be re-run; the commands are given in each
section.

New code lives in:

| Path | What |
|---|---|
| `rust/sigil-witness/proofs/` | standalone crate: abstract model (`tla.rs`), transcription of the witness logic (`model_rust.rs`), the world and step checker (`world.rs`, `checker.rs`), Kani harnesses (`kani_proofs.rs`), tests (`tests/`), differential driver (`src/bin/diff_driver.rs`, `diff/differential.py`), mutation testing (`mutants.py`) |
| `rust/sigil-witness/fuzz/` | cargo-fuzz targets, `run.sh`, `coverage.sh`, the bug-1 reproducer in `regressions/` |
| `tests/test_rust_verification_findings.py` | Python `expectedFailure` test for the one finding that also affects the reference |

Neither crate is a member of `rust/Cargo.toml`; the shipped workspace and its tests are
unchanged. `src/` was not modified: bugs are recorded as ignored tests (below).

## 0. Summary

| Kind of evidence | Scope | Result |
|---|---|---|
| Kani proofs on the transcription of the record logic | every record state (unbounded i128 generations), vote histories of ≤ 2 votes | each SPEND/RELEASE step is a TLA+ `Spend`/`Release` step or a stutter, and an invariant implying one tid per `(sigil, gen)` is inductive |
| Kani proofs on shipped functions | quorum arithmetic (all `usize`); `votes_of_seal`, lock monotonicity, parser (bounded) | proved; the parser harness finds bug 1 at 8 bytes |
| Bounded exhaustive check of the real witness | every state reachable with a 363-op alphabet (3 sigils, 7 headers, gens 0..3, 276 death-proof shapes) | 521 states, 189,123 checked transitions, no violation; all 11 seeded mutants killed (see §3.4) |
| Fuzzing (libFuzzer) | 5 targets, 40 min each | 64.9 M executions; 1 crash (bug 1) |
| Differential vs the Python reference | 4,000 episodes, 143,594 steps; 56,040 JSON texts | votes byte-identical; divergences are bugs 2 and 5 or deliberate strictness |

Bugs: **6**. One High (bug 3, a deep request bricks the store), one Medium (bug 4, CPU
amplification; it also affects the reference), four Low. No bug lets an honest Rust
witness vote two tids at one `(sigil, gen)`.

## 1. The abstraction function and the refinement claim

The TLA+ model is `formal/Sigil.tla`. `formal/SigilProofs.tla` has the same `Spend` and
`Release` with unbounded generations, and TLAPS proves `Spec => []Safety` for it. The
state of one honest witness `w` for a sigil `s` is `gen[w][s]`, `bound[w][s]` and the
votes `<<c, w, s, g, t>>` it has cast. **α** maps the Rust witness to it, per sigil:

```
α(rec).gen   = rec.gen
α(rec).bound = rec.tid          (None ↦ NoTid; "!contested" ↦ a phantom tid no header has)
α(rec).votes = { <<v.constellation, v.witness, s, v.gen, v.tid>> : v ∈ rec.votes }
α(no record) = (0, NoTid, {})
```

`rec.header`, `rec.vote`, `rec.abstain` and `rec.log` are not part of the TLA+ state. The
three components of α are exactly what STATUS returns (§5.3), so α is computed through the
public API (`proofs/src/tla.rs`).

**Refinement claim.** Every call of `Witness::spend`, `Witness::release` and
`Witness::status` on the real witness either changes nothing in α (a stutter), or is:

* for SPEND: `Spend(w, s, t)` with `t = H("transition", req.header)` and `g = GenOf(t, s)`.
  The guard holds in the pre-state, `s` is named once in `t`'s header, `Home[s] = ConsOf(w)`,
  and the post-state is `(g, t)` with `votes' = votes ∪ {<<c, w, s, g, t>>}`; or
* for RELEASE: `Release(w, s)`. `bound ≠ NoTid` and the post-state is `(gen + 1, NoTid)` with
  votes unchanged. Its guard `DeathProofExists(bound)` holds in a vote set containing the
  votes the proof carries, which are genuinely signed.

Every other sigil is unchanged (frame), and every vote the witness lets out is in its
STATUS before the reply (persist-before-answer).

`checker.rs` checks exactly this after every step, in every harness below. "Genuinely
signed" is checked against a spec-level oracle (`World::oracle_dead`), written from SPEC §3.9
and not from `proofs.rs`. It counts only votes the harness or the witness actually signed,
so the cryptographic assumption (Ed25519 unforgeability) is the only one used.

## 2. What is proved (Kani 0.68.0, CBMC 6.11.0)

`cd rust/sigil-witness/proofs && cargo kani` (harnesses in `src/kani_proofs.rs`).

| Harness | Code | Bounds / assumptions | Result | Time |
|---|---|---|---|---|
| `quorum_intersection_all_n` | real `charter::{faults, quorum}` | every `n: usize` | no panic or overflow; `q ≤ n`; for `n ≥ 1`: `3f < n`, `2q ≥ n + f + 1` (Lemma 1 counting), `2f < q` (Lemma 2 counting) | 4.6 s |
| `quorum_of_empty_charter_is_zero` | real `quorum` | `n = 0` | documents bug 2 (`q(0) = 0`, the spec gives 1) | <1 s |
| `init_satisfies_invariant` | transcription | | `Init` satisfies `inv`, and α(empty) = TLA+ `Init` | <1 s |
| `spend_refines_tla_and_preserves_invariant` | `model_rust::spend_core` | every record (gen any i128 in [0, 2^62], tid any of 6 or CONTESTED, vote, abstain free), absent records, any authorisation/expiry outcome, `0 ≤ g < 2^62`, any tid; histories of ≤ 2 earlier votes | stutter, or exactly TLA+ `Spend`; a conflict carries only our vote for another tid at the same gen; `inv` preserved | KANI_SPEND |
| `release_refines_tla_and_preserves_invariant` | `model_rust::release_core` | same | only from bound non-contested records with a valid proof; exactly TLA+ `Release`; `gen + 1` never overflows; `inv` preserved | KANI_RELEASE |
| `votes_of_seal_never_overrides` | real `proofs::votes_of_seal` | one entry whose own keys are each present or not, plus at most one override key naming any seal field; symbolic integer values | KANI_VOS | KANI_VOS_T |
| `lock_eval_monotone_in_time` | real `locks::evaluate` | locks of depth ≤ 2 (≤ 2 children) over `after`/`before`/`never`/absent-`sig` leaves; any i64 times and clock | KANI_LOCK | KANI_LOCK_T |
| `parse_no_panic_7` | real `json::parse` | every input of ≤ 7 bytes without `.`, `e`, `E` (floats are out of Kani's reach) | KANI_P7 | KANI_P7_T |
| `parse_no_panic_8_finds_bug_1` | real `json::parse` | same, ≤ 8 bytes | KANI_P8 | KANI_P8_T |

`inv` (per record) says: the generation is in range, and a bound record's generation is
below 2^62. The stored vote is for the bound tid at the current generation and is in the
history. Every vote in the history is at or below the current generation, and one at the
current generation is either the stored vote or the reason for `abstain`. The history has
one tid per generation. Because `inv` is inductive and implies "one tid per `(sigil, gen)`",
the transcription never equivocates, for any number of steps.

**Limits of the proofs.**
(1) The record-logic proofs are about a transcription (`model_rust.rs`), not the shipped
`witness.rs`. §3 checks that the shipped code behaves exactly like the transcription
(reply, α, and the hidden fields read back from the store) on every reachable state of the
bounded world and on every fuzzed step. That is a test of the link, not a proof.
(2) The vote history is bounded at two votes. Symbolic-length `Vec`s made CBMC run out of
memory (10 GB). The invariant's clauses are per vote and per pair of votes, so one step
interacts with at most two of them; the generalisation is an informal argument.
(3) Signature checks, hashing and the store are outside the proofs: `authorised`,
`expired` and `proof_ok` are free booleans. The death-proof checker is covered by §3–§5.

**Panic freedom (audit).** On attacker-controlled paths, `witness.rs`, `proofs.rs`,
`locks.rs`, `charter.rs` and `model.rs` use `expect` only where the value was established
just before (`authorises` returns `Some` only for a string sigil and an integer `expires`;
`vote_payload` of a vote it just built; `verify_many(&[c])[0]`). Arithmetic on generations
is bounded by `authorises` (`g < 2^62`), so `rec.gen += 1` cannot overflow (proved above).
`json.rs` slices `str`s only at ASCII positions, except in `hex4` (bug 1). Recursion is
bounded: the parser at 256 levels, `well_formed` at depth 8, and `evaluate` runs only on
well-formed locks. The state mutex is poisoned only by a panic under the lock, and no code
under the lock can panic. Deliberately out of scope: `std::process::abort` in `store.rs`,
which is fail-closed by design.

## 3. Bounded exhaustive check of the real witness

`cargo test --release --test refinement_bfs -- --nocapture` (`SIGIL_BFS_FULL=1` for the
full alphabet).

The **world** (`proofs/src/world.rs`) has three constellations. C has 4 members and q = 3,
with `w0` as the witness under test. D has 1 member and q = 1. R is a 1-member rogue
constellation that homes no sigil. There are sigils `a`, `b` (homed at C) and `c` (homed
at D). Seven headers have the shapes of `formal/MC.tla`: a same-generation conflict, a
two-home transition, release to generation 1, a jump to generation 2, and more.

The **alphabet** is SPEND of any sigil in any header, with the owner's or an intruder's
signature and a live or expired authorisation, plus STATUS. Then RELEASE with a death proof
of any of these shapes: either input of the bound header; seal or votes; from the home, the
rogue or the other constellation; for a phantom tid, for the bound tid itself, or for any
header's tid; with all, or all but one, of the harness-held members; with or without `w0`'s
own votes; with a correct or a wrong parcel.

The **search** is breadth-first to a fixpoint. Each transition restores a real `Witness`
from the parent state's full record table into a fresh redb store on tmpfs and runs one
checked step. It then reopens the store and compares every stored field (`gen`, `tid`,
`vote`, `abstain`, `header`) with the transcription. State identity is the record table
without `log`; `log` is write-only in `witness.rs`, and §3.3 checks that dropping it
changes no reply. Initial states are the empty store plus one a successor's ADOPT could
write: `a` CONTESTED, and `b` bound with `abstain` because the key already voted another
tid at that generation.

| Alphabet | States | Transitions checked | Depth | Time |
|---|---|---|---|---|
| reduced (150 ops) | 521 | 78,150 | 11 | 158 s |
| full (363 ops) | 521 | 189,123 | 11 | 590 s |

No violation of refinement, transcription, frame, persist-before-answer, one tid per
`(sigil, gen)`, death-proof soundness, or **completeness**: every proof the spec oracle
accepts (with exactly-`{witness, time, sig}` seal entries), the witness accepts too.

**What this proves.** For this world and alphabet, every reachable state of the real
witness has been visited, and every step from it is an allowed TLA+ step. Generations,
tids and sigils are few; the Kani proofs cover the record logic for all values.

### 3.3 Restart equivalence

`cargo test --release --test restart_equivalence`. 720 random steps (12 seeds × 60) were
run twice: on a continuously running witness, and on one closed and reopened from its redb
store, with logs dropped, before every step. Replies are byte-identical, and so is the final
state. This shows persist-before-answer leaves nothing a reply depends on in memory only,
and that `log` never influences a reply.

### 3.4 Mutation testing of the harness

`python3 rust/sigil-witness/proofs/mutants.py` copies `rust/` to a scratch directory,
applies one edit to `sigil-witness/src`, and runs the reduced bounded check against it.

MUTANT_TABLE

## 4. Fuzzing (cargo-fuzz 0.13.2, libFuzzer, nightly)

`rust/sigil-witness/fuzz/run.sh SECONDS [targets]`. Seeds come from
`cargo run --release --manifest-path proofs/Cargo.toml --bin gen_seeds -- fuzz/corpus`.
`fuzz/coverage.sh` reports line coverage of `src/`.

| Target | What it checks | Execs (40 min) | Edges (cov) | Line coverage of the key file |
|---|---|---|---|---|
| `json_roundtrip` | parser never panics; canonical output is ASCII, re-parses to the same value and is a fixpoint | 57,882,230 | 988 | json.rs 81.5 % |
| `witness_ops` | structured SPEND/RELEASE/STATUS sequences (≤ 48 ops) and mutated requests/proofs, raw sigils, varying clock; every step checked by `checker.rs` (refinement, transcription, one tid per gen, death-proof soundness) | 482,142 | 5,170 | witness.rs 81.5 %, proofs.rs 89.1 % |
| `witness_http_body` | raw bodies through the server's parse → object → field path, sequences of up to 8 messages, then the same checks | 3,974,073 | 3,401 | json.rs 81.2 %, witness.rs 67.6 % |
| `locks_eval` | evaluate never panics; batch = single verification; monotone in time; true ⇒ well formed; agreement with a spec oracle on generated locks (shape rules, depth 8, 64 nodes, sig/multi/hash/equivocation/time semantics) | 2,133,942 | 3,405 | locks.rs 99.2 % |
| `proofs_verify` | mutated seals, death proofs and equivocation proofs: no panic; batch = single; accepted ⇒ valid per the spec oracle (genuine votes only); `votes_of_seal` never lets an entry override the seal | 404,767 | 4,085 | proofs.rs 97.1 % |

The only crash was bug 1, found by `json_roundtrip` after about 10,000 executions with the
known-bug filter off (`FUZZ_FLAGS=--no-default-features`). The filter
(`fuzzgen::hits_known_parser_panic`) is on by default so the campaigns could run past it.
LibFuzzer flagged "slow units" during runs that overlapped an out-of-memory CBMC run; re-run
alone, every one takes under 1 s including start-up.

## 5. Differential testing against the Python reference

```
cargo build --release --manifest-path rust/sigil-witness/proofs/Cargo.toml --bin diff_driver
PYTHONPATH=. python3 rust/sigil-witness/proofs/diff/differential.py --episodes 3000 --seed 7
PYTHONPATH=. python3 rust/sigil-witness/proofs/diff/differential.py --episodes 1000 --seed 11 --empty-charter
PYTHONPATH=. python3 rust/sigil-witness/proofs/diff/differential.py --canonical --texts 50000 --corpus rust/sigil-witness/fuzz/corpus/json_roundtrip
```

The same random requests are serialised once with `json.dumps` and sent to an in-process
`sigil.witness.Witness` and to the real Rust `Witness` (through `diff_driver`). The requests
are SPENDs over 14 parcels with sig/multi/time/hash/equivocation/never locks in 3–4
constellations, multi-input headers, varied expiry and signers, and 15 % structurally
mutated. The RELEASEs carry death proofs from the home, the rogue or other constellations,
with all or some signers, with the witness's own votes, and 25 % mutated. There are also
STATUS calls. Replies are compared byte for byte, and after each agreed step the STATUS of
every sigil is compared too. The reference was merged at `fc8a82b` (successor-bound FREEZE,
CONTESTED candidates); those changes are rotation-only and do not touch
SPEND/RELEASE/STATUS of a non-contested record.

| Run | Steps | Agreed votes / releases / conflicts | SAFETY | STATE | PANIC | Other divergences |
|---|---|---|---|---|---|---|
| seed 7, 3,000 episodes | 108,753 | 15,221 / 8,072 / 2,578 | 0 | 0 | 0 | 427 seal entries with extra keys; 135 integers beyond i128; 24 + 6 + 1 other deliberate type strictness (see below) |
| seed 11, 1,000 episodes, empty charter registered | 34,841 | 4,980 / 2,497 / 861 | **56, all bug 2** | 0 | 0 | as above |
| canonical, 56,040 texts (incl. 6,040 fuzz-corpus files) | | 39,720 identical encodings | **5 different encodings (bug 5)** | | 0 | 8,080 refused by Rust only (integers beyond i128, lone surrogates); 0 accepted by Rust only |

**Deliberate strictness** is behaviour where Rust abstains and Python votes or releases.
It is a liveness difference only, documented in the source.
* A seal vote entry with keys besides `{witness, time, sig}` is refused (`proofs.rs`).
* JSON outside Rust's value range is refused: integers beyond i128, lone surrogates,
  NaN/Infinity, nesting deeper than 256.
* Header inputs must be `[string, int]` pairs. Python unpacks any 2-iterable, so a
  2-character string `"ab"` counts as an input, and it tolerates non-string sigils in
  other inputs.
* Header generations must be below 2^62.
* A death proof's `gen` must be an integer. Python's `==` also accepts `false` and `1.0`.

**Harness artefacts found and fixed on the way** (not bugs).
* The first STATE divergence came from the driver mutating objects it shared with the
  in-process reference: the world's locks, the witness's stored `header`, and the vote dicts
  that the in-process `Witness.status()` returns by reference. Over HTTP these are copies.
  The driver now deep-copies before mutating.
* The same sharing had silently disabled most spends, which explained the early low vote
  counts.

## 6. Bugs found

Every bug has a failing test, ignored with `BUG n: …` in
`rust/sigil-witness/proofs/tests/bugs.rs`. Run them with
`cargo test --release --test bugs -- --ignored`.

| # | Severity | Where | Summary | Test |
|---|---|---|---|---|
| 1 | Low–Medium | `json.rs` `Parser::hex4` | remote panic on `"\u` + non-ASCII bytes | `bug1_…`, `fuzz/regressions/json_roundtrip/hex4-char-boundary`, Kani `parse_no_panic_8_finds_bug_1` |
| 2 | Low | `charter.rs` `faults`/`quorum` | `quorum(0) = 0`: an empty charter accepts unsigned seals and death proofs | `bug2_…`, differential `--empty-charter` |
| 3 | **High** (availability) | `witness.rs` + `store.rs` + `json::MAX_DEPTH` | one deep but accepted SPEND makes the store unloadable: the witness never restarts | `bug3_…` |
| 4 | Medium (DoS) | `locks.rs` `Ctx::ev` "equivocation"; also `sigil/locks.py` | lock evaluation costs #nodes × #proofs signature checks | `bug4_…`, `tests/test_rust_verification_findings.py` |
| 5 | Low | `json.rs` `py_float_repr` | exact-tie floats are encoded differently from Python, so hashes differ | `bug5_…`, differential `--canonical` |
| 6 | Low (latent, fails open) | `store.rs` `load` | `frozen` stored as a successor hash (the reference's format since `fc8a82b`) loads as not frozen | `bug6_…` |

None of them lets an honest Rust witness sign two tids at one `(sigil, gen)`. Bug 2 lets the
witness release on evidence the reference rejects, but only for a home constellation that
violates the §8 fault assumption, so it falls outside the theorem.

### Bug 1: the JSON parser panics on `\u` followed by non-ASCII bytes

`Parser::hex4` slices `&self.src[self.i..self.i + 4]`. When a multi-byte UTF-8 character
straddles `i + 4`, this panics with "byte index is not a char boundary".

**Reproduction.**
```
curl -X POST --data-binary $'{"sigil":"\\u111\xc3\xa9"}' http://127.0.0.1:PORT/v0/status
```
The reply is empty (curl exit 52). The server prints the panic and keeps serving, because
the binary unwinds on panic.

**Impact.** Any unauthenticated client can drop its own connection and spam the log; a
build with `panic = "abort"` would crash the witness. Kani finds the bug with 8-byte inputs
and proves the parser panic-free for all inputs of ≤ 7 bytes without `.`, `e` or `E`.
libFuzzer found it in about 10,000 executions.

**Fix.** Work on bytes:
```rust
fn hex4(&mut self) -> Result<u32, ParseError> {
    let h = self.s.get(self.i..self.i + 4).ok_or_else(|| self.err("truncated \\u escape"))?;
    let mut v = 0u32;
    for &c in h {
        v = v * 16 + (c as char).to_digit(16).ok_or_else(|| self.err("invalid \\u escape"))?;
    }
    self.i += 4;
    Ok(v)
}
```
Also consider a catch-panic layer in `server.rs` that answers 500, as the reference does.

### Bug 2: `quorum(0) = 0`

`faults(n) = n.saturating_sub(1) / 3` gives `f = 0`, so `q = 0`. SPEC §7 has
`f = ⌊(n−1)/3⌋ = −1` and `q = 1`, and Python's `(n - 1) // 3` agrees.

**Effect.** For a registered constellation whose charter lists no witnesses (both
implementations load one, since `verify_chain` does not reject it):
* `verify_seal` accepts a seal with no member votes;
* `proves_dead` accepts a death proof made only of non-member votes;
* `verify_chain` accepts a successor charter with zero signatures.

The differential run with an empty charter registered shows 56 RELEASEs that the reference
refuses.

**Fix.** Either `pub fn quorum(n: usize) -> usize { if n == 0 { 1 } else { n - faults(n) } }`,
or (better, in both implementations) make `verify_chain` reject charters with an empty or
duplicated witness list, as `charter_body` already does when one is created.

### Bug 3: a deeply nested SPEND bricks the store

The server accepts bodies nested up to 256 levels (`json::MAX_DEPTH`). The witness stores
the authorisation (`salt`, `header`, `unlock`) inside `record.log[i].auth`, two levels
deeper than in the body. On the next start, `Store::open` parses each record with the same
limit, fails with `corrupt store value: … nesting too deep`, and the witness refuses to
start.

**Reproduction.** `bug3_deep_request_bricks_the_store_on_restart` sends a SPEND whose
`salt` is 254 nested arrays: the body depth is exactly 256, the witness votes, and reopening
the store fails. The salt is chosen by the parcel's owner, so anyone can do this to every
witness of a constellation with one request each. It is fail-closed (no equivocation), but
the witness stays down until an operator edits the store by hand. The reference is not
affected: it refuses such requests while hashing, and its loader accepts far deeper JSON.

**Fix.** Parse store values without the request limit, for example a
`json::parse_with_limit(bytes, MAX_DEPTH + 16)` used by `store::load`, since stored values
are produced by the witness itself. In addition, or instead, refuse requests deeper than
`MAX_DEPTH - 8` in `server.rs`. Add the test as a regression.

### Bug 4: equivocation-lock evaluation is O(#nodes × #proofs)

Each `{"op":"equivocation"}` node runs `verify_equivocation` on every proof in
`unlock.equivocations`. A proof whose cheap field checks pass but whose signatures do not
verify costs three Ed25519 verifications (a failed batch check, then two single ones).

**Cost.** With 63 nodes, the work is 63 × #proofs. A 1 MiB unlock holds about 1,400 proofs,
which is roughly 5 s of CPU per evaluation; a failed SPEND evaluates twice. SPEND runs on
the async worker threads (only RELEASE uses `spawn_blocking`), so a handful of concurrent
requests stall every reply.

**Measurements.** With 60 proofs: 1 node takes 5.6 ms, 63 nodes take 229 ms (ratio 41). The reference has the same
structure (ratio 44, inside its single dispatch lock).

**Fix.**
* Memoise per proof in `Ctx`, as `has_sig` already is: a
  `RefCell<Vec<Option<bool>>>` indexed like `equivocations`. Check the cheap `a.witness`
  filter first.
* Cap the number of equivocation proofs and signatures considered, for example 16.
* Run `spend` in `spawn_blocking`.

### Bug 5: canonical float encoding differs from Python on exact ties

When two shortest digit strings both round-trip to a double and are exactly equally close
to it, Python's `repr` (David Gay's dtoa) picks the even last digit; Rust's `{:e}` picks
the other one. Example: `1966098015293243369E-3`; Python gives `1966098015293243.2`, Rust
gives `…243.3`. The double is exactly `…243.25`.

**Impact.** `H(...)` of any value containing such a float differs between the
implementations, including `sigil_of` and the `tid`. The owner signs the reference's tid,
so the Rust witness only refuses: an interop and liveness bug, not theft. The canonical
differential hit it 5 times in 39,725 texts both sides accept.

**Fix.** After `{:e}`, if decrementing or incrementing the last digit gives a string that
also parses to `x` and lies at exactly the same distance, choose the even digit. Equal
distance is checked exactly by comparing the decimal midpoint with `x`'s exact expansion,
e.g. `format!("{:.1100e}", x)` trimmed. Alternatively port Python's
`float_repr_style='short'` rule. Add these five cases to `tests/gen_vectors.py`.

### Bug 6: the `frozen` entry in the reference's new format loads as not frozen

Since `fc8a82b`, the reference stores `frozen` as the hash of the one successor charter it
froze for (`true` only in older stores). `store.rs` documents the same entry kinds, but
`load` sets `out.frozen = value == Json::Bool(true)`, so a hash loads as **not frozen**, and
the witness would vote again after a restart.

**Impact.** Latent: the Rust witness never freezes and does not read Python's sqlite stores.
But it fails open, and it will matter as soon as FREEZE is ported or stores are migrated.

**Fix.**
```rust
"frozen" => out.frozen = !matches!(value, Json::Bool(false) | Json::Null)
```
Keep the successor hash, so a later FREEZE for a different successor is refused, as in the
reference.

### Informational (no test)

* **Batch Ed25519 verification.** `ed25519-dalek`'s batch equation is documented as able to
  accept signatures that single verification rejects. This only concerns signatures made
  with keys their holder controls, and is already noted in BENCHMARKS.md. In every fuzzing
  campaign above, with honest and randomly corrupted signatures, batch and single
  verification gave the same verdict.
* **Storage growth without stamps.** The Rust witness refuses `--stamps`. Anyone can create
  sigils homed here, and each SPEND stores up to 1 MiB of authorisation forever. The
  reference relies on stamps for this.
* **Rotation divergence (expected).** Since `fc8a82b`, the reference RELEASEs a CONTESTED
  record by removing its candidates. The Rust witness has no rotation and answers "nothing
  to release" for a CONTESTED record restored from a store. It cannot produce one itself.

## 7. Tools

| Tool | Status |
|---|---|
| cargo-fuzz 0.13.2 + libFuzzer (nightly) | installed (`cargo install cargo-fuzz`); llvm-tools-preview for coverage |
| Kani 0.68.0 (CBMC 6.11.0, toolchain nightly-2026-08-21) | installed (`cargo install --locked kani-verifier && cargo kani setup`) |
| Verus | **not installed**: it is distributed only as GitHub release binaries, and the proxy answers 403 for `github.com/verus-lang/verus/releases` and `api.github.com/repos/verus-lang/verus/releases`. TLS verification was not disabled. Kani plus the exhaustive check of the real code stand in for it |
| proptest / quickcheck | not needed: the exhaustive check and the hand-written PRNG in `restart_equivalence.rs` cover the same ground without new dependencies |
| TLC / TLAPS | not re-run here; `formal/check.sh` covers them (VERIFICATION.md) |
