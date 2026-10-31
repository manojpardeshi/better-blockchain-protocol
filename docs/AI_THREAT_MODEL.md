# Sigil against an AI-scale adversary

This document asks whether Sigil is **"AI proof"**: safe against an adversary that
is tireless, automated, and far better and faster than humans at finding bugs,
forging and spamming at machine scale, social-engineering operators, coordinating
collusion, and exploiting timing and cryptanalysis. It is a companion to
[VERIFICATION.md](VERIFICATION.md) (what is machine-checked) and
[VERIFY_RUST.md](VERIFY_RUST.md) (the Rust witness).

The honest conclusion first:

> **What rests on mathematics, a smarter attacker cannot beat.** Quorum
> intersection, signature unforgeability, hash collision-resistance and the
> machine-checked safety theorem (TLAPS, [VERIFICATION §1](VERIFICATION.md#1))
> hold no matter how capable the adversary is. A super-human attacker gets
> *nothing* extra against the core double-spend theorem.
>
> **What rests on assumptions, a smarter attacker attacks the assumption, not the
> math.** Every Sigil guarantee is conditioned on: at most *f* Byzantine
> witnesses per constellation it relies on; honest **operators** of those
> witnesses; **secret keys**; **unbroken** Ed25519 / RSA-FDH / BLAKE2b; and
> **honestly backed-up dossiers**. An AI adversary is dangerous precisely because
> it is better at *breaking assumptions at scale*: manufacturing Sybil witnesses,
> phishing operators, finding the one implementation bug, and racing timing
> windows. The residual risk is almost entirely here.

Three real defects were found while writing this (one critical), all recorded as
`expectedFailure` regression tests in `tests/redteam/test_redteam.py` and
summarised in [§3](#3-findings). They were **not** fixed, per the task.

---

## 1. The math / assumption split

| Guarantee | Rests on | Can a super-human attacker beat it? |
|---|---|---|
| No sigil consumed by two complete transitions (SPEC §8 Theorem) | Quorum intersection + Ed25519 unforgeability + `≤ f` Byzantine per home | **No**, given the assumptions. TLAPS-proved for all sizes, single version ([VERIFICATION §1](VERIFICATION.md#1)) |
| At most one seal per `(sigil, gen)` (Lemma 1) | Quorum intersection | **No** (proved) |
| Death proofs are sound (Lemma 2) | Quorum intersection, home-bound evidence (§3.9) | **No** (proved) |
| Honest witness never equivocates (`HonestNoEquiv`) | Local record + durable store | **No** (proved; store inspected by hand) |
| Witnesses cannot steal (SPEC §8) | Holder re-checks the owner's unlock (validate §6.4) | **No**: even an all-Byzantine quorum cannot forge the owner's signature |
| Witnesses cannot inflate | Holder checks conservation (validate §6.5) | **No** — *except* via BUG-1, a cache defect, not a math break ([§3](#3-findings)) |
| Fees cannot censor; witness cannot discriminate | Blind RSA-FDH stamps | Only by breaking RSA-FDH or the blinding |
| Safety holds across rotation | ADOPT + evidence logs | Bounded-checked only (not size-free); see [§2.11](#211-rotation-and-succession) |
| Liveness / recovery / deep confirmation | **Honest-majority of current operators, honest STATUS answers** | **Yes, at the assumption**: see BUG-2 and [§2.5](#25-timing-partitions-and-gossip-withholding) |

The rest of this document walks each AI-relevant capability, cites the existing
defence and why it works, and gives the residual risk and a concrete mitigation
with a priority (**P0** = before any real value; **P1** = before public testnet;
**P2** = before v1 / audit; **P3** = research).

---

## 2. Threats

### Ranked summary (top risks first)

| # | Threat | Property at stake | Rests on | Residual risk | Priority |
|---|---|---|---|---|---|
| T1 | **Implementation bugs** (the AI finds the one flaw) | all | correct code | **High** — BUG-1 is a live counterfeit; code is unaudited | **P0** |
| T2 | **Key / dossier theft via agent subversion** (prompt injection) | no theft | key secrecy | **High** for AI-held wallets | **P0** |
| T3 | **Operator compromise ≥ f per constellation** (phish/bribe/Sybil) | double-spend safety of that home | `≤ f` honest operators | **High**; AI scales phishing & Sybil | **P1** |
| T4 | **Griefing via lying STATUS / partitions** | liveness, funds-stuck | honest STATUS, honest majority | **Medium** (BUG-2: third-party harm) | **P1** |
| T5 | **Resource exhaustion** (CPU/mem/storage amplification) | availability | rate limiting (stamps) | **Medium**; stamps off by default | **P1** |
| T6 | **Long-range forgery** by retired keys | safety of old history | long unbonding + deep confirmation | **Medium** | **P2** |
| T7 | **Deanonymisation from dossiers** | privacy | nothing today (ancestry is in the clear) | **High** for privacy | **P2/P3** |
| T8 | **Quantum / cryptanalysis** | everything | unbroken Ed25519 / RSA-2048 | **Low now, Catastrophic later** | **P2 plan, P3 impl** |
| T9 | **Economic attacks** (stamp pricing, bond sizing, griefing) | availability, slashing economics | unspecified params | **Medium**; params undefined | **P2** |
| T10 | **Protocol-level attacks** on recovery / swaps | liveness, atomicity | protocol design | **Medium** (swap hostage, [§2.8](#28-multi-party-swaps-and-counter-party-attacks)) | **P2** |

---

### 2.1 Finding implementation bugs and protocol-level attacks (T1)

**Property at stake:** everything. A single bug in `sigil/` or `rust/` can defeat a
theorem that is otherwise airtight — the math is only as good as its transcription.

**What defends it, and why.** This is Sigil's strongest area *on paper*: the core
theorem is TLAPS-proved for all sizes ([VERIFICATION §1](VERIFICATION.md#1), 842
obligations); rotation, expiry and deep confirmation are TLC-model-checked with
mutation tests ([§2](VERIFICATION.md#2)); the real Python witness is conformance-
tested against the proved model ([§3](VERIFICATION.md#3)); and the Rust witness is
Kani-proved, exhaustively bounded-checked, fuzzed (65 M execs) and differentially
tested, finding six bugs now fixed ([VERIFY_RUST.md](VERIFY_RUST.md)). An AI
adversary that is good at finding bugs is exactly what this machinery is built to
pre-empt.

**Residual risk — High.** The verification is scoped to the **witness protocol
under idealised crypto**. It explicitly does **not** cover the **wallet**, the
**holder-side validator**, persistence, networking, the server, or liveness
([VERIFICATION §5](VERIFICATION.md#5)). That is where the value actually is to a
holder — and it is where this review found **BUG-1**, a critical counterfeit in
`sigil/validate.py`'s verifier cache (see [§3](#3-findings)). The validator is the
party "with a real incentive to check" (whitepaper §3); a bug there breaks
conservation for everyone, with no witness or key needed. The code is unaudited
(README "Status").

**Mitigation (P0):**
1. Extend formal/fuzz coverage to the **holder-side validator** and the **wallet**
   (selection, pledge bookkeeping, recovery, deep-confirmation orchestration). The
   new `tests/redteam/conserve.py` fuzzer is a start; a TLA+/property model of
   `Verifier` with a mutation test for the cache would have caught BUG-1.
2. Treat the verifier cache as security-critical: cache identity must bind
   `tid → (header, body)`, re-checked on every hit (BUG-1 fix).
3. Keep the red-team harness ([§4](#4-the-red-team-harness)) in CI; it is designed to
   be re-run at length by an automated attacker's budget.

---

### 2.2 Spam / Sybil identities at machine scale (T3 ingest, T5)

**Property at stake:** availability of witnesses and of gossip; integrity of the
charter registry.

**What defends it, and why.** Three deliberate choke points:
* **Stamps** (`sigil/stamps.py`): a SPEND can be made to require a blind RSA-FDH
  stamp the witness sold in advance. Spam then costs money, and because the stamp
  is blind the witness still cannot discriminate (whitepaper §9). This is the
  intended anti-spam primitive.
* **Gossip caps** (`sigil/gossip.py`, [WIRE.md Caps](WIRE.md)): ≤ 64 chains, 1024
  versions, 64 proofs, 16 forks per message; ≤ 10 000 new constellations per store;
  proofs against keys outside a known charter are refused, so throwaway keys cannot
  grow the store. Every item is verified before storage.
* **Permissionless but self-verifying charters:** anyone can mint a constellation,
  but a holder's **trust policy** (`sigil/validate.py::TrustPolicy`) decides which
  to accept, so Sybil constellations are inert unless someone trusts them.

**Residual risk — Medium.**
* **Stamps are off by default.** `Network.create_constellation(..., stamps=False)`
  is the default, and the Rust witness refuses `--stamps` entirely
  ([VERIFY_RUST §6 Informational](VERIFY_RUST.md)). A witness without stamps has
  **no rate limit**: anyone can create sigils homed there and force unbounded work
  and storage ([§2.6](#26-resource-exhaustion-t5)).
* The gossip constellation cap (10 000) bounds *count*, not *size*: one ~1 MiB
  message can register a charter listing 14 000 witnesses (measured,
  `tests/redteam/resources.py::gossip_store_growth`).
* Sybil *trust* is a social problem: an AI that manufactures plausible
  constellation reputations could get a holder to trust a home it controls → then
  [§2.3](#23-corrupting-a-constellation-t3) applies directly.

**Mitigation:**
* **P1:** make stamps (or an equivalent proof-of-work / rate limit) the default for
  any witness exposed to the open network; have the Rust witness implement them.
* **P2:** bound gossip by *total bytes and total witnesses*, not just item counts.
* **P2:** a reputation/stake floor for trust-policy admission, so an AI cannot
  cheaply manufacture a trustworthy-looking home.

---

### 2.3 Corrupting a constellation: collusion & bribery ≥ f (T3)

**Property at stake:** the double-spend safety of parcels homed in that
constellation.

**What defends it, and why.** The theorem assumes `≤ f = ⌊(n−1)/3⌋` Byzantine
members. **Below f**, the explorer and TLAPS show nothing can seal a double-spend,
block a spend, or see value (SPEC §7 table). **At or above f**, two things still
hold and are the real defence:
1. **Witnesses still cannot steal or inflate** — holders re-check the owner's
   unlock and conservation (validate §6.4–6.5), proven in SPEC §8 "Holders cannot
   be robbed". A corrupt quorum can only double-spend a parcel *whose own owner
   colludes*, and doing so **leaves equivocation proofs** that slash its bonds.
2. **Per-holder trust and per-parcel homes** contain the blast radius: a corrupt
   home affects only parcels homed there, and holders can demand stronger homes for
   large value (SPEC §9 "Payment size").

**Residual risk — High against the assumption.** An AI adversary is *better than
humans at reaching `f`*: it can phish or bribe operators continuously, and — more
cheaply — **stand up its own constellation** and persuade holders to trust it (then
it owns the quorum outright). Quorum intersection is a theorem; "`≤ f` of them are
honest" is a bet on people. The red-team `beyond_f` mode confirms the cliff: with
`b = f+1` the explorer finds a double-spend within tens of seeds
(`test_beyond_fault_bound_breaks_safety`) — the protection is the assumption, not
luck.

**Mitigation:**
* **P1:** independence requirements for operators (jurisdiction, org, hosting)
  recorded in charters so holders can judge correlation; an AI colluder is hardest
  when the `n` operators genuinely cannot coordinate.
* **P2:** size bonds so that a double-spend's expected loss (slashed bonds, via the
  equivocation proofs it necessarily emits) exceeds its gain — see
  [§2.9](#29-economic-attacks-t9).
* **P2:** deep confirmation against the current charter for high value (already in
  the wallet) narrows the window for a *retired* corrupt quorum ([§2.7](#27-long-range-forgery-t6)).

---

### 2.4 Social engineering / phishing of key holders & operators (T2, T3)

**Property at stake:** key secrecy (holders) and operator honesty (witnesses) —
both **assumptions**, not math.

**What defends it, and why.** Very little in-protocol, by design: Sigil assumes
keys are secret and operators honest. The one structural help is that **witness
compromise alone cannot steal** (§2.3), so phishing an *operator* is far less
rewarding than phishing a *holder's* signing key — there is no "validator key that
moves funds". Equivocation by a bribed operator is self-slashing (SPEC §7).

**Residual risk — High.** This is the classic place a super-human social engineer
wins, and Sigil offers no magic. An AI that phishes a **holder's** key spends that
holder's parcels outright (indistinguishable from the owner). An AI that phishes a
**dossier backup** can impersonate the holder to a recipient only if it also has
keys, but can **destroy** the holder's money by deleting the only copy (the dossier
*is* the money; README, `wallet_store.py`).

**Mitigation:**
* **P0 for AI-held wallets:** the agent-policy locks of [§5](#5-protecting-ai-agents-that-hold-wallets)
  (`sigil/agent_policy.py`): co-signing, time-delays with an owner veto window, and
  claw-back so a single phished/injected agent key cannot move large value alone.
* **P1:** hardware-key and threshold-signing guidance for high-value holders;
  encrypted, redundant dossier backup (the format already supports it).
* **P2:** operator key hygiene, HSM-backed witness keys, and short witness terms
  with long bond unbonding so a compromised operator key ages out quickly.

---

### 2.5 Timing, partitions and gossip withholding (T4)

**Property at stake:** liveness and recovery — and, via BUG-2, the funds of an
*honest third party*.

**What defends it, and why.** Safety is **timing-independent**: a network attacker
can delay but not reorder or double-seal (SPEC §7 "network attacker"), because
there is no ordering to attack and seals are monotone. Recovery from a stuck
multi-party transition uses **death proofs** (SPEC §5.2), which are timeless facts.
The **expiry + clock-skew** rule (SPEC §4 rule 3, model-checked `MC_expiry`) stops a
delayed in-flight request from binding a coin after the owner has given up. Gossip
**withholding** is tolerated as long as one honest relay path exists; every item
self-verifies ([WIRE.md Threats](WIRE.md)).

**Residual risk — Medium, and this is where BUG-2 lives.** The pledge-release rule
3 and deep confirmation both **trust STATUS answers**. A Byzantine witness within
*f* that lies on STATUS ("I hold no binding") during a partition can induce an
honest owner — following the spec exactly — to create a second binding, which after
rotation turns an **honestly sealed** coin CONTESTED and fails deep confirmation for
an innocent recipient (BUG-2, [§3](#3-findings)). Safety (no double spend) is
preserved; the whitepaper's "only the equivocator loses" is not — the loss lands on
a third party. An AI adversary is ideal for this: it can hold exactly the right
STATUS lie across exactly the right partition and rotation timing.

The open "pathological split" problem (whitepaper §10.7) is the same family: if
votes split without any quorum and some witnesses are unreachable forever, no death
proof exists and the honest party's input stays locked. An AI that controls network
timing maximises how often this happens.

**Mitigation:**
* **P1:** do not treat STATUS as authoritative for liveness decisions. For rule 3,
  keep the pledge unless the owner holds **signed** evidence (a death proof) or
  re-uses the same tid; for ADOPT/deep confirmation, treat a sibling attested only
  by `≤ f` members (never a quorum, never a seal) as a non-binding *attempt*, so one
  lying witness cannot contaminate an honestly sealed binding (BUG-2 fix).
* **P2:** bond counter-parties and retry swaps against fresh witnesses to shrink the
  pathological-split window (whitepaper §10.7); a formal treatment is open.

---

### 2.6 Resource exhaustion (T5)

**Property at stake:** availability (CPU, memory, disk per request) and the cost
asymmetry between attacker and victim.

**What defends it, and why.** Stamps bound request rate when enabled; the 1 MiB body
cap bounds any single request; gossip caps bound a message; lock evaluation is
total and linear, and the equivocation-proof memoisation fix (Rust/Python BUG-4,
[VERIFY_RUST §6](VERIFY_RUST.md)) removed the worst amplifier.

**Residual risk — Medium**, measured by `tests/redteam/resources.py`:
* **CPU:** a sub-MiB SPEND with a large `sig`/`multi` lock tree forces thousands of
  Ed25519 verifications. Measured: a **272 KiB** request → **3 780 verifies ≈ 0.58 s
  CPU** on this VM (≈ 14 verifies/KiB); a full 1 MiB request is ≈ **2 s CPU**. This
  generalises Rust BUG-4 beyond equivocation locks to ordinary multi-sig. SPEND runs
  on the async worker in Rust (only RELEASE uses `spawn_blocking`), so a handful of
  concurrent such requests stall the witness.
* **Storage:** each accepted SPEND logs the full authorisation (salt + header +
  unlock) forever; measured ≈ **800 KiB stored per request**, ratio ≈ 1.0, and logs
  never compact (`store.py` docstring). Without stamps this is free to the attacker
  ([VERIFY_RUST §6 Informational](VERIFY_RUST.md)).
* **Memory:** one ~1 MiB gossip message registers a 14 000-witness charter.

An AI adversary with many cheap IPs and the default (stampless) witness can keep a
constellation's witnesses CPU-bound and fill their disks.

**Mitigation:**
* **P1:** stamps (or PoW) default-on for open witnesses; run SPEND on a blocking
  pool; cap lock nodes × keys evaluated per request (e.g. 16), and cap stored
  authorisation size.
* **P2:** log compaction (`store.py` notes it is deliberately omitted); bound total
  gossip bytes and witnesses, not just counts.

---

### 2.7 Long-range forgery with retired keys (T6)

**Property at stake:** safety of *old* history — a retired quorum, colluding with an
owner, forging a seal for a sigil really consumed elsewhere.

**What defends it, and why.** Retired witnesses who forge **leave equivocation
proofs**, and **deep confirmation** (SPEC §9, `wallet.deep_confirm`, model-checked
`MC_deep`) asks the *current* charter whether each old `(s, g, tid)` is really
bound; `f+1` current confirmations mean ≥ 1 honest current witness vouches, and
honest witnesses inherit every real binding on rotation (SPEC §5.4). Bonds with
unbonding longer than the deep-confirmation horizon keep the forgers slashable.

**Residual risk — Medium.** Deep confirmation is **off by default** (`deep_threshold
= None`) and only as strong as the *current* honest majority and the `f+1`
threshold (`MC_deep_mutant` shows `f` is unsafe). BUG-2 shows a way to make deep
confirmation *falsely fail* for honest history. And the whole mechanism depends on
bonds that are correctly sized and still bonded (economics, [§2.9](#29-economic-attacks-t9)).
An AI that retired-key-forges will do so at the exact moment bonds have unbonded.

**Mitigation:**
* **P2:** sensible default `deep_threshold`; charters that **publish** minimum bond
  and unbonding so holders can set it; fix BUG-2 so deep confirmation does not
  false-negative.
* **P3:** the recursive-proof roadmap ([RECURSIVE_PROOFS.md](research/RECURSIVE_PROOFS.md))
  replaces full-ancestry dossiers with succinct proofs, which also removes the
  retired-key window for the ancestry (the proof, not the seals, carries validity).

---

### 2.8 Multi-party swaps and counter-party attacks (T10)

**Property at stake:** atomicity and the honest party's ability to recover.

**What defends it, and why.** A swap is one transition sealed only if *every* input
is sealed (SPEC §5, `sigil/swap.py`), and each party checks it is paid before
signing (`atomic_swap` `_pays`). If a counter-party equivocates its own input first,
the honest party uses a **death proof** to release and recover (SPEC §8 "Generations
exist so honest parties can recover"; `tests/test_recovery_rotation.py`).

**Residual risk — Medium.** Recovery needs a death proof to *exist*. If a malicious
counter-party gets the honest party's unlock, binds only the honest input, and then
never produces a conflicting spend (just walks away), **no death proof exists** and
the honest input stays locked until expiry lets the pledge go — and if witnesses are
unreachable, longer (the whitepaper §10.7 open problem; reproduced in this review:
an input bound but never completed leaves the honest party stuck until expiry). An
AI counter-party will choose exactly this "bind and vanish" strategy and time it
against the victim's expiry and any pending rotation.

**Mitigation:**
* **P2:** the expiry rule already bounds the lock-up to `expires + skew` for
  reachable witnesses; make swaps default to short expiries and automatic
  retry-with-fresh-salt, and **bond counter-parties** so "bind and vanish" costs
  them. A complete fix for the unreachable-forever case is open (whitepaper §10.7).

---

### 2.9 Economic attacks: stamp pricing, bond sizing, griefing (T9)

**Property at stake:** whether honesty is the profit-maximising strategy —
availability (can spam be priced out?) and slashing (does a double-spend lose more
than it gains?).

**What defends it, and why.** The mechanism exists: stamps price attention, bonds
back honesty with equivocation locks ideally homed elsewhere with long unbonding
(whitepaper §9). Crucially, **a corrupt-quorum double-spend necessarily emits
equivocation proofs** (SPEC §7), so slashing is automatic and needs no governance —
the economic defence has teeth the moment bonds are real.

**Residual risk — Medium.** The **parameters are unspecified** (ROADMAP Phase 4:
"Stamp pricing and bond sizing" ⬜). Nothing today says how large a bond must be
relative to the value a constellation homes, or how stamps are priced against
spam cost. An AI adversary optimises against whatever numbers are chosen:
under-priced stamps → spam; under-sized bonds → profitable double-spend where
gain > slashed bonds; griefing where the attacker burns others' stamps / forces
recovery work for little cost.

**Mitigation:**
* **P2:** define bond ≥ (value homed × safety margin) and make charters publish it;
  price stamps to exceed marginal spam cost; model griefing (who pays for a forced
  release / retry) and ensure the griefer's cost ≥ the victim's. This is a design
  task, not code.

---

### 2.10 Deanonymising holders from dossier metadata (T7)

**Property at stake:** holder privacy.

**What defends it, and why.** *Witnesses* are blind: they see only
`sigil = H(home, lock, salt)` and a body hash, never asset, amount, payer, payee or
graph (SPEC §3.2, `test_security::test_witnesses_are_blind_to_value`). Stamps are
unlinkable. So the *infrastructure* learns nothing.

**Residual risk — High for privacy.** The **recipient sees the whole ancestry**:
every amount, lock key (a pseudonymous identity), home, memo and vote timestamp in
the dossier it is handed, and through swaps the counter-asset's history too
([RECURSIVE_PROOFS.md §1](research/RECURSIVE_PROOFS.md): in a mixing economy a payee's
dossier covered 83 % of all transitions after 2 400 steps). An AI adversary excels
at linking pseudonymous keys and timing across these dossiers to deanonymise
holders — no cryptographic break needed, just graph analysis at scale.

**Mitigation:**
* **P3:** the recursive-proof roadmap ([RECURSIVE_PROOFS.md](research/RECURSIVE_PROOFS.md),
  ROADMAP Phase 3) hides ancestry behind a succinct proof whose public statement
  carries only output commitments and the trust footprint — this is the real fix and
  is already designed and prototyped (Plonky2 toy, RISC-V cycle counts).
* **P2 interim:** issuer *redemption* (re-mint short-history coins) and guidance to
  rotate receiving keys and avoid long-lived mixing coins.

---

### 2.11 Rotation and succession (T3/T4 at the seam)

**Property at stake:** safety and liveness across membership change.

**What defends it, and why.** FREEZE/ADOPT carry owner-signed evidence that
successors verify without trusting the handler; a lying predecessor can omit but not
invent (SPEC §5.4). The implemented sibling-contested ADOPT is TLC-checked
(`MC_rot_sibling*`), and the two rotation bugs found earlier are fixed and held as
regression tests ([VERIFICATION §4](VERIFICATION.md#4)). FREEZE now binds to one
successor (no charter fork).

**Residual risk — Medium.** Rotation safety is **bounded-checked only**, never
size-free ([VERIFICATION §5](VERIFICATION.md#5)): 2 versions, 2 sigils, ≤ 4
transitions, gens 0..1. Succession (dead-man takeover) is **unimplemented** (ROADMAP
Phase 4 ⬜), so a constellation that dies strands its parcels — an AI adversary that
can DoS a small constellation into death permanently freezes its value. BUG-2
exploits the rotation seam specifically.

**Mitigation:** **P2** extend the rotation proof toward more versions; implement and
model-check succession with partition tolerance (whitepaper §10.4). **P1** fix BUG-2.

---

## 3. Findings

All three are recorded as `expectedFailure` tests in
`tests/redteam/test_redteam.py` (each with a full scenario/impact/fix docstring) and
reproduced by the harness. None was fixed, per the task. `python3 -m unittest
discover` stays green (expected failures count as passes).

| # | Severity | Where | One line | Test |
|---|---|---|---|---|
| BUG-1 | **Critical** (conservation / counterfeit) | `sigil/validate.py` `Verifier._verify` cache | A warm recipient's verifier cache skips re-validating a cached transition's body, so a malicious **payer** reuses a public ancestor tid (e.g. the genesis) with a forged body and an output minted from thin air; a 1000-supply asset inflated a recipient to ~1e9. Cold recipients reject. | `Finding1Conservation` |
| BUG-2 | Medium (liveness / third-party griefing) | `sigil/wallet.py` rule-3 release + `deep_confirm`, `sigil/witness.py` ADOPT | A Byzantine witness within *f* that lies on STATUS induces an honest owner to create a second binding; after rotation the honestly sealed coin is CONTESTED and deep confirmation fails for an innocent holder. Safety holds; "only the equivocator loses" is violated. | `Finding2InducedEquivocation` |
| BUG-3 | Low (robustness / contract) | `sigil/witness.py` `authorises` | A malformed non-dict `unlock` raises `AttributeError` (not caught) instead of `Rejected` from in-process `Witness.spend`; the HTTP server masks it as 400, no state mutated. | `Finding3MalformedLeak` |

**BUG-1 is the headline.** It needs no witness, no key, and no `f`-corruption — only
that the recipient previously verified a shared ancestor (the asset genesis id is
public). It breaks the single property the whitepaper leans on to say "witnesses
cannot inflate": holder-side conservation. Suggested fix: make the hash-identity and
genesis checks independent of the `_ok` cache (verify `transition_id(header)==tid`
and `body_hash(body)==header.body` for the presented dossier entry before the cache
short-circuit), or cache verified `(header, body)` identity and re-check on a hit.

---

## 4. The red-team harness

`tests/redteam/` plays the AI adversary against the in-process reference, in three
engines, all driving the **real** `sigil` code:

* **`model.py`** — a randomised + lightly guided schedule explorer over adversarial
  action sequences: Byzantine witnesses up to and beyond *f*, an equivocating owner,
  forged/malformed messages, strongest-assemblable death proofs, crash/restart
  through the durable store, and rotation at adversarial moments. After every step
  it checks **S1** (no double consumption) and **S2** (no honest witness convicted).
  Guidance biases toward releasing/rotating from states with sibling bindings.
* **`conserve.py`** — a payment-level fuzzer over the real `Wallet`: random payments
  and atomic swaps, checking **S3** (honest wallet never equivocates), **S4**
  (value conserved across the economy) and **S5** (no parcel held without its key).
* **`resources.py`** — CPU / memory / storage amplification probes with measured
  ratios.

**Fast by default** (`python3 -m unittest tests.redteam.test_redteam`, ~8 s), with
env knobs for long runs (`python3 -m tests.redteam.runner`;
`SIGIL_REDTEAM_SEEDS/STEPS/TIME/NS/BEYOND`). **Mutation-checked:** seeding the real
witness to accept any death proof is caught as S1; an amnesiac generation floor is
caught as S2 (`MutationChecks`), so the checks have teeth.

### Statistics (long run on this 4-core VM)

<!-- REDTEAM_STATS -->
*(filled in below from `python -m tests.redteam.runner` with
`SIGIL_REDTEAM_SEEDS=300 SIGIL_REDTEAM_STEPS=200`, `SIGIL_REDTEAM_BEYOND=1`.)*

Key results, independent of the exact counts:
* **No S1/S2 violation** in any within-fault-bound configuration (n = 4, 7, 10;
  with and without crash/restart; with rotation) across the whole long run.
* **Beyond the bound** (b = f+1), S1 (a double-spend) is found quickly — the harness
  confirms safety is the *assumption* `≤ f`, enforced by quorum-intersection math,
  not an artefact.
* **No conservation (S4) violation** in the honest payment fuzzer; BUG-1 is reached
  only by the deliberate `cache_attack`, i.e. it is a validator-cache defect, not a
  property of honest flows.
* **Amplification** (resources): ~14 Ed25519 verifies/KiB of SPEND (≈ 2 s CPU per
  1 MiB request); ≈ 800 KiB durable storage per SPEND (ratio ≈ 1.0); one ~1 MiB
  gossip message registers a 14 000-witness charter.

---

## 5. Protecting AI agents that hold wallets (T2)

`sigil/agent_policy.py` (new; edits nothing else) expresses an owner's spending
policy for an autonomous agent's keys **in the existing lock language**, so the
constraints are enforced by witnesses and re-checked by recipients — **not** by the
agent's own, prompt-injectable code. Tested end-to-end in `tests/test_agent_policy.py`.

| Policy | Lock | What it stops |
|---|---|---|
| Co-signing | `all(sig(agent), sig(owner))` | A subverted agent cannot move the parcel without an out-of-band owner signature. |
| k-of-n threshold | `all(sig(agent), multi(k, cosigners))` | Large reserves need *k* independent approvers besides the agent. |
| Time-delay + veto window | `any(all(sig(agent), after(T)), all(sig(agent), sig(owner)))` | A large payment settles alone only after `T`; the owner has until `T` to claw back or decline to co-sign. |
| Owner claw-back | `any(sig(owner), all(sig(agent), after(T)))` | The owner can reclaim the float at any time; the agent spends alone only after the window. |
| Cooperative payee allow-list | `all(sig(agent), sig(payee))` | The agent can complete a payment only with the named payee's counter-signature. |
| Capped float (structural) | small parcels `sig(agent)`, large parcels co-signed; owner sets the refill cadence | Approximates a per-period cap without on-chain state. |

**What the lock language *cannot* express** (enumerated in
`agent_policy.WHAT_LOCKS_CANNOT_EXPRESS`): (1) **unilateral payee allow-listing** —
a lock constrains the spender, never the output, and witnesses are blind to
outputs, so "only pay Acme" needs Acme's cooperation or an off-parcel policy signer
that inspects outputs before co-signing; (2) **true rolling per-period caps**,
(3) **rate/velocity limits**, (4) **aggregate-value conditions across inputs** — all
need state a stateless per-parcel lock cannot hold (delegate to a co-signing policy
server that keeps the counter); (5) **conditioning on asset/amount/memo/payee** —
the only non-signature predicates are the `after`/`before` clock and hash
preimages; (6) **in-place key revocation** — disabling a compromised agent key means
re-homing the parcels (claw-back), not editing the lock; (7) **owner veto as a
positive stop** — the time-delay gives a *window*, not an explicit halt signal.

The honest summary: the lock language gives an owner **co-signing, delay, and
claw-back**, which together defang a single injected agent key for large value. It
**cannot** give amount-aware or stateful policy on its own; those belong to a
co-signing **policy server** (itself a `sig` in the lock) that applies the stateful
rules before signing — reducing the trust in the agent to the trust in that server.

---

## 6. Crypto agility and the post-quantum plan (T8)

**Property at stake:** *everything*. Sigil is Ed25519 (votes, unlocks, charters),
RSA-FDH (stamps) and BLAKE2b (hashes). A cryptographically-relevant quantum computer
(CRQC) breaks Ed25519 and RSA outright; it does **not** break BLAKE2b's
collision/preimage resistance beyond a Grover square-root (BLAKE2b-256 → ~128-bit
preimage, acceptable; a later move to a 384/512 digest is a parameter change, not a
redesign). So the exposure is **signatures**, and it is total: a CRQC forges votes
(double-spend without controlling `f`), forges unlocks (**steal** any parcel —
defeating the "witnesses cannot steal" guarantee, since that guarantee rests on the
owner's signature being unforgeable), forges charters, and unblinds/forges stamps.

This is **not** a live risk (no CRQC exists), but **harvest-now-decrypt-later** does
not apply to signatures the way it applies to encryption — a forged signature is
only useful while a key is still trusted. The danger is a CRQC arriving before keys
and bonds have rotated out. Plan now; implement when the ecosystem has standardised
hybrids.

### 6.1 Declaring schemes in charters and locks

The clean seam is **domain-tagged, scheme-labelled keys**. Today `Sig` is
`Ed25519 over "sigil/v0/sig/" ‖ tag` (SPEC §2) and a lock leaf is `{op:"sig", pk}`.
Make the scheme explicit and negotiable:

* **Charters** gain a `schemes` field: the signature scheme(s) a version's witnesses
  use for votes, e.g. `["ed25519", "ml-dsa-65"]`. A vote then carries `scheme`, and a
  seal is valid if a quorum of **matching-scheme** votes verifies — or, for a
  **hybrid** window, each witness signs *both* and a vote is a pair, counted only if
  both verify. Charter signatures themselves move to the hybrid first (they are
  rarest and highest-value).
* **Locks** gain scheme-labelled leaves: `{op:"sig", pk, scheme}` and a **hybrid**
  via the *existing* combinators — `all(sig(pk_ed), sig(pk_mldsa))` for
  "both must sign" (defence-in-depth while one scheme is young) or
  `any(sig(pk_ed_retiring), sig(pk_mldsa))` during migration. No new lock op is
  needed for hybrids; only `sig`/`multi` leaves need a `scheme` tag, and verification
  dispatches on it. This is a strict, backward-compatible extension: a v0 leaf with
  no `scheme` means `ed25519`.
* **Stamps** (RSA-FDH) are the awkward one: blind signatures over lattices are less
  mature. Shorter term, stamps can move to a larger RSA modulus (buys little against
  a CRQC) or to a **hash-based / VOPRF** stamp; this is a research item, and because a
  stamp only authorises *attention* (not value), a stamp break is a spam problem, not
  a theft problem — lower priority than votes and unlocks.

### 6.2 Candidate schemes and cost impact

Using the numbers already in the repo — Ed25519 is **≈ 40–53 µs verify, ≈ 25 µs sign**
in Rust, pubkey 32 B, signature 64 B ([BENCHMARKS.md](BENCHMARKS.md)); a seal at
n = 4 is ≈ 3 votes and a dossier is **≈ 2.4 KB JSON / 0.9 KB binary per hop**, of
which the seal (n votes × 64 B sig + 32 B key) dominates
([RECURSIVE_PROOFS.md §1](research/RECURSIVE_PROOFS.md)); and the ZK-recursion work
notes **signatures are 96–98 % of the guest cost** and recommends **signature-scheme
agility in charters** as a lever.

| Scheme | Pubkey | Sig | Verify (rel.) | Role |
|---|---:|---:|---|---|
| Ed25519 (today) | 32 B | 64 B | 1× (~50 µs) | baseline |
| **ML-DSA-65** (Dilithium, FIPS 204) | ~1.95 KB | ~3.3 KB | ~0.5–2× verify, sign slower | primary PQ signature for votes/unlocks |
| **SLH-DSA-128s** (SPHINCS⁺, FIPS 205) | 32 B | ~7.9 KB | fast verify, **very slow sign**, huge sig | conservative hash-based fallback / charters |
| Hybrid Ed25519 + ML-DSA-65 | ~1.98 KB | ~3.36 KB | ~both | migration window |

**Cost impact, concretely:**
* **Seals / dossiers blow up.** A vote's signature goes 64 B → ~3.3 KB (ML-DSA) and
  the key 32 B → ~2 KB. A 3-vote seal goes from ~0.9 KB to **~16 KB** (ML-DSA) or
  **~24 KB** (SLH-DSA). At the measured ~2.4 KB/hop today, a PQ dossier is roughly
  **7–10× larger per hop**, and dossier growth is already the #1 open problem
  (whitepaper §10). **This makes the recursive-proof roadmap (Phase 3) not optional
  but a prerequisite for PQ at scale** — a succinct proof hides and compresses the
  now-bulky signatures, which is exactly why that doc flags PQ: "STARK recursion is
  PQ-plausible; any SNARK wrap is not" ([RECURSIVE_PROOFS.md](research/RECURSIVE_PROOFS.md)).
* **Verification CPU** rises modestly for ML-DSA (comparable order to Ed25519) but
  loses Ed25519 batch verification's 30–50 % saving ([BENCHMARKS.md](BENCHMARKS.md))
  unless a lattice batch scheme is used.
* **Unlock size** per input grows the same ~50× for the signature, affecting request
  bodies (the 1 MiB cap and the storage-per-SPEND amplification of
  [§2.6](#26-resource-exhaustion-t5) both get worse).

### 6.3 Migration path

1. **P2 (now, no code):** freeze the above as a design — `scheme`-tagged keys,
   `schemes` in charters, hybrid via `all(...)` — and add `scheme` to the SPEC §2
   signature definition as a reserved, defaulting-to-`ed25519` field so v1 wire is
   forward-compatible.
2. **P2:** implement scheme dispatch in `crypto.verify`/`sign` and `locks` behind the
   tag, with Ed25519 the only registered scheme (no behaviour change, tested by the
   existing suite). This is the trivial, do-now part; the rest waits.
3. **P3 (when hybrids standardise / a CRQC looms):** register ML-DSA-65; roll
   **charters** to hybrid first (rarest, highest value), then **new parcels'** locks
   to hybrid, then deprecate Ed25519-only acceptance via trust policy. Old parcels
   migrate by being **spent into** hybrid-locked outputs (an ordinary payment — no
   fork, no coordinated flag day, because there is no shared chain; this is where
   Sigil's "no global structure" actually helps).
4. **P3:** PQ or VOPRF stamps; and land recursive proofs (Phase 3) so PQ signatures
   do not explode dossiers.

**Do not implement beyond step 2 now** — the hybrid standards and libraries are still
settling, and premature lattice code is its own attack surface.

---

## 7. What cannot be made "AI proof" — and why

Being honest about the ceiling:

1. **Compromise of your own keys / agent subversion.** If an AI phishes or injects
   the holder's (or its agent's) signing key, it *is* the owner to every witness and
   recipient. The agent-policy locks ([§5](#5-protecting-ai-agents-that-hold-wallets))
   raise the bar (co-sign, delay, claw-back) but cannot help if *every* required key
   is compromised. No value system can.
2. **`≥ f` corruption of a home you trust.** Quorum intersection is a theorem *given*
   `≤ f` Byzantine; it says nothing once an AI bribes/phishes/Sybils past `f`. Then
   it can double-spend colluding owners' coins (leaving slashable proofs) — but the
   math is spent. Sigil contains the blast radius (per-parcel homes, per-holder
   trust) and makes cheating self-incriminating; it cannot make `f+1` honest people
   out of `f+1` bribed ones.
3. **Losing your dossier.** The dossier *is* the money; an AI that deletes your only
   backup destroys your funds, with no ledger to restore from (README). Redundant
   encrypted backup is the only answer, and it is operational, not cryptographic.
4. **Pathological liveness** (whitepaper §10.7): a counter-party that binds and
   vanishes while the right witnesses are unreachable forever can lock an honest
   input with no death proof available. An AI that owns network timing maximises
   this. A complete fix is open.
5. **Traffic/metadata analysis and dossier graph linkage.** Until recursive proofs
   land, recipients see full ancestry; an AI linking pseudonymous keys and timings
   deanonymises holders with *no* crypto break. Succinct proofs fix the data exposure
   but not all network-level timing analysis.
6. **A cryptographic break** (CRQC, or a flaw in Ed25519/RSA-FDH/BLAKE2b). Then the
   signature-based guarantees — including "witnesses cannot steal" — fall. Crypto
   agility ([§6](#6-crypto-agility-and-the-post-quantum-plan-t8)) is the only hedge,
   and it is a bet that migration beats the break.

Everything resting on **quorum-intersection math, signature unforgeability, and the
machine-checked theorem** is as AI-proof as mathematics is. Everything resting on
**people (honest operators, honest majority, secret keys, careful backups),
unspecified economics, un-proved code paths (wallet/validator), and un-broken
crypto** is exactly where a tireless, super-human adversary concentrates — and is
where this review found a critical counterfeit (BUG-1), a third-party griefing path
(BUG-2), and the measured amplification and privacy gaps above. Sigil's design
*minimises* the assumption surface (no global state, no infrastructure that can
steal, self-slashing cheating); it does not — and cannot — eliminate it.
