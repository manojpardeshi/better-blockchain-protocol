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

This review found **six defects**, summarised in [§3](#3-findings). After the
review, BUG-1 (critical: a counterfeit through the holder's verifier cache),
BUG-3 and BUG-4 were fixed, along with the `sig`/`multi` CPU amplification
(`MAX_KEYS`); their tests are now regression tests in
`tests/redteam/test_redteam.py`. **Two remain open** as `expectedFailure` tests,
both design questions: BUG-5 (swap hostage) and BUG-6 (bond self-claim). The sixth, BUG-2, was fixed upstream in
parallel and is now a regression test. Three more attack hypotheses tested here
(dossier merge poisoning, the default trust policy accepting a payer's rogue home,
and shared-control locks accepted as payment) were also fixed by that wallet work.
Per the task, nothing in `sigil/` was changed here.

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
| Liveness / recovery / deep confirmation | **Honest-majority of current operators, honest STATUS answers, cooperative counter-parties** | **Yes, at the assumption**: see BUG-2 (fixed), BUG-4, BUG-5 and [§2.5](#25-timing-partitions-and-gossip-withholding) |
| Slashing deters a corrupt quorum | Bond economics + who can satisfy the equivocation branch | **Yes, by design flaw**: the equivocator claims its own bond (BUG-6, [§2.9](#29-economic-attacks-t9)) |

The rest of this document walks each AI-relevant capability, cites the existing
defence and why it works, and gives the residual risk and a concrete mitigation
with a priority (**P0** = before any real value; **P1** = before public testnet;
**P2** = before v1 / audit; **P3** = research).

---

## 2. Threats

### Ranked summary (top risks first)

Threat ids (T1–T10) are stable labels used in the section headings; the first
column is the rank.

| Rank | Threat | Property at stake | Rests on | Residual risk | Priority |
|---|---|---|---|---|---|
| 1 (T1) | **Implementation bugs** (the AI finds the one flaw) | all | correct code | **High**: BUG-1 is a live counterfeit; code is unaudited | **P0** |
| 2 (T2) | **Key theft via agent subversion** (prompt injection) | no theft | key secrecy | **High** for AI-held wallets | **P0** |
| 3 (T9) | **Economic attacks** (bond self-claim, stamp pricing, bond sizing) | slashing economics, availability | lock design + unspecified params | **High**: BUG-6 voids slashing against the cheater | **P1** |
| 4 (T3) | **Operator compromise ≥ f per constellation** (phish / bribe / Sybil) | double-spend safety of that home | `≤ f` honest operators | **High**; AI scales phishing and Sybil | **P1** |
| 5 (T10) | **Protocol-level attacks** on recovery / swaps | liveness, atomicity | cooperative counter-party | **Medium–High** (BUG-5 swap hostage, [§2.8](#28-multi-party-swaps-and-counter-party-attacks)) | **P1** |
| 6 (T5) | **Resource exhaustion** (CPU / memory / storage amplification) | availability | rate limiting (stamps) | **Medium**; stamps are opt-in in both witnesses | **P1** |
| 7 (T6) | **Long-range forgery** by retired keys | safety of old history | long unbonding + deep confirmation | **Medium** (BUG-4 lets a payer skip deep confirmation) | **P1** |
| 8 (T7) | **Deanonymisation from dossiers** | privacy | nothing today (ancestry is in the clear) | **High** for privacy, no loss of funds | **P2/P3** |
| 9 (T4) | **Griefing via lying STATUS / partitions** | liveness | honest STATUS, honest majority | **Low–Medium** (BUG-2 fixed; induced owner equivocation remains) | **P2** |
| 10 (T8) | **Quantum / cryptanalysis** | everything | unbroken Ed25519 / RSA-2048 | **Low now, catastrophic later** | **P2 plan, P3 implementation** |

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
* **Stamps are opt-in.** `Network.create_constellation(..., stamps=False)`, the
  Python daemon (`sigil.witnessd --stamps`) and, since the merged port, the Rust
  witness (`sigil-witness --stamps`) all default to *no* stamps. A witness without
  stamps has **no rate limit**: anyone can create sigils homed there and force
  unbounded work and storage ([§2.6](#26-resource-exhaustion-t5)). Note also that
  `/v0/sell_stamp` blind-signs for anyone who asks: the payment step is outside the
  protocol, so a deployment must put it behind a real payment channel or stamps
  cost nothing.
* The gossip constellation cap (10 000) bounds *count*, not *size*: one ~1 MiB
  message can register a charter listing 14 000 witnesses (measured,
  `tests/redteam/resources.py::gossip_store_growth`).
* Sybil *trust* is a social problem: an AI that manufactures plausible
  constellation reputations could get a holder to trust a home it controls → then
  [§2.3](#23-corrupting-a-constellation-t3) applies directly.

**Fixed on main (relevant here).** Wallets no longer trust every constellation they
hear about: by default a wallet trusts only the constellations known when it was
created plus its home, and charters learned from a payer's dossier are used to
verify seals but never trusted unless the owner calls `trust` (`91269ff`). This
review confirmed the earlier hole: a payer could home its coin in a one-member
constellation it runs, seal a double spend there, and both payees accepted. That
attack now fails with "untrusted constellation".

**Mitigation:**
* **P1:** make stamps (or an equivalent proof-of-work / rate limit) the default for
  any witness exposed to the open network, and gate `/v0/sell_stamp` behind payment.
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
   colludes*, and doing so **leaves equivocation proofs** against its keys, so its
   votes stop counting for every holder who learns them. (Those proofs are meant to
   slash its bonds too, but today the cheater can claim its own bond first: BUG-6.)
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
moves funds". Equivocation by a bribed operator is self-incriminating (SPEC §7),
though not yet self-slashing (BUG-6).

Two wallet fixes on main (`91269ff`) close phishing-adjacent holes this review also
reproduced: a wallet now accepts a payment only into an address it **issued**,
exactly (home, lock and salt), so a payer can no longer credit it with a parcel
locked `any(sig(victim), sig(payer))` that the payer can claw back; and `receive`
merges only the **verified ancestry** of what it accepts, never over entries it
already holds, so a payer can no longer overwrite the victim's own history with
garbage and make its coins unprovable. The witness rotation calls `/v0/freeze`
and `/v0/adopt` on the Rust witness now need an admin token, which removes an
unauthenticated way to freeze a witness.

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

**Property at stake:** liveness and recovery, and (via BUG-2, now fixed) the
spendability of an *honest third party's* funds.

**What defends it, and why.** Safety is **timing-independent**: a network attacker
can delay but not reorder or double-seal (SPEC §7 "network attacker"), because
there is no ordering to attack and seals are monotone. Recovery from a stuck
multi-party transition uses **death proofs** (SPEC §5.2), which are timeless facts.
The **expiry + clock-skew** rule (SPEC §4 rule 3, model-checked `MC_expiry`) stops a
delayed in-flight request from binding a coin after the owner has given up. Gossip
**withholding** is tolerated as long as one honest relay path exists; every item
self-verifies ([WIRE.md Threats](WIRE.md)).

**Residual risk — Low–Medium (was Medium; BUG-2 is now fixed).** The pledge-release
rule 3 **trusts STATUS answers**. A Byzantine witness within *f* that lies on STATUS
("I hold no binding") during a partition can induce an honest owner, following the
spec exactly, to sign a second transition at the same generation. Before the merged
fix, the next rotation then turned the **honestly sealed** coin CONTESTED and deep
confirmation failed for an innocent recipient (BUG-2, [§3](#3-findings)): safety
held, but "only the equivocator loses" did not. Main now lets `deep_confirm`
present the seal it holds, and the witness settles a CONTESTED record onto the
sealed candidate (SPEC §8 Lemma 1), so the third party is no longer stranded. What
remains is that a liar can still *induce* a second owner signature; it is harmless
today because the first one can never reach a quorum, but it is a standing reason
not to treat STATUS as evidence. An AI adversary is ideal for this kind of attack:
it can hold exactly the right lie across exactly the right partition and rotation.

The open "pathological split" problem (whitepaper §10.7) is the same family: if
votes split without any quorum and some witnesses are unreachable forever, no death
proof exists and the honest party's input stays locked. An AI that controls network
timing maximises how often this happens.

**Mitigation:**
* **Done on main:** seal settlement of CONTESTED records (the BUG-2 fix proposed
  here and landed independently in `91269ff`/`eca6edd`, Python and Rust).
* **P2:** do not treat STATUS as authoritative for liveness decisions. For rule 3,
  prefer re-authorising the *same* tid over signing a new one, and keep the pledge
  unless the owner holds signed evidence (a death proof).
* **P2:** bond counter-parties and retry swaps against fresh witnesses to shrink the
  pathological-split window (whitepaper §10.7); a formal treatment is open.

---

### 2.6 Resource exhaustion (T5)

**Property at stake:** availability (CPU, memory, disk per request) and the cost
asymmetry between attacker and victim.

**What defends it, and why.** Stamps bound request rate when enabled; the 1 MiB body
cap bounds any single request; gossip caps bound a message; lock evaluation is
total and linear; and the equivocation-proof memoisation fix (Rust/Python bug 4 of
[VERIFY_RUST §6](VERIFY_RUST.md)) plus the merged **64-proof cap** per unlock
(`MAX_EQUIVOCATIONS`) removed the worst amplifier, equivocation locks.

**Residual risk — Medium**, measured by `tests/redteam/resources.py`:
* **CPU (fixed after the review):** the proof cap did not touch `sig`/`multi`
  locks, so one 272 KiB SPEND forced ~3,780 Ed25519 verifications. A lock may
  now name at most `MAX_KEYS = 64` keys in all (SPEC §3.5, Python and Rust),
  and each key's signature is checked once per evaluation, so no SPEND checks
  more than 64 signatures (`test_spend_cpu_amplification_measured`).

An AI adversary with many cheap IPs and the default (stampless) witness can keep a
constellation's witnesses CPU-bound and fill their disks.

**Mitigation:**
* **P1:** stamps (or PoW) default-on for open witnesses; memoise `has_sig` in
  `sigil/locks.py` as Rust already does; cap the signature checks one request may
  trigger (for example 64, which no 64-node lock needs to exceed by much) and the
  keys in one `multi`; cap the stored authorisation size (salt length, header
  inputs, unlock contents).
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
threshold (`MC_deep_mutant` shows `f` is unsafe). Worse, **the threshold is applied
per parcel** (BUG-4): a payer who wants to avoid deep confirmation splits one large
payment into parcels just under the threshold. A wallet with `deep_threshold=1000`
accepted 9 990 units as ten parcels of 999 and ran deep confirmation zero times.
An automated adversary probes exactly this kind of parameter first. BUG-2 (now
fixed) showed a way to make deep confirmation *falsely fail* for honest history.
The mechanism also depends on bonds that are correctly sized, still bonded and
actually punitive, which BUG-6 undermines ([§2.9](#29-economic-attacks-t9)). An AI
that forges with retired keys will do so at the exact moment bonds have unbonded.

**Mitigation:**
* **P1:** apply `deep_threshold` to the total value of one payment (and per
  counter-party per time window), not per parcel (BUG-4).
* **P2:** a sensible default `deep_threshold`; charters that **publish** minimum
  bond and unbonding so holders can set it.
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

**Residual risk — Medium–High (BUG-5).** Recovery needs a death proof to *exist*.
A malicious counter-party that receives the honest party's unlock can submit **only
the honest input** (binding it to the swap) and then never sign, submit or spend its
own input. The swap can never complete, yet no death proof exists: one needs another
input sealed to a different transition at its generation, or a quorum of votes for
one (SPEC §3.9), and only the counter-party can create that. **Expiry does not
help**: it only stops a witness from *newly* binding (SPEC §5.1), and the honest
input is already bound. `Wallet.abort` reports "no proof that the transition is
dead", and the honest coin stays locked for as long as the counter-party likes: a
free option, or a ransom. This needs no equivocation, no Byzantine witness and no
network fault, so it is distinct from the whitepaper §10.7 "pathological split" and
contradicts its §7 table ("cannot hurt anyone else; honest co-signers recover"). The
reference `atomic_swap` hides it because it signs both sides in one process. An AI
counter-party will use exactly this "bind and vanish" strategy.

**Mitigation:**
* **P1 (protocol, cheap):** each party adds a small **kill-switch** input it
  controls and withholds that input's unlock until it sees the other side's inputs
  bound. If the counter-party stalls, it spends the kill switch elsewhere at the
  swap's generation, which yields the death proof. With kill switches the worst case
  becomes a bounded free option, not a hostage. Alternatively, never hand over an
  unlock before holding the other side's. Build swaps this way in `sigil/swap.py`.
* **P2:** bond counter-parties; a complete fix for the unreachable-forever split of
  §10.7 is still open.

---

### 2.9 Economic attacks: stamp pricing, bond sizing, griefing (T9)

**Property at stake:** whether honesty is the profit-maximising strategy —
availability (can spam be priced out?) and slashing (does a double-spend lose more
than it gains?).

**What defends it, and why.** The mechanism exists: stamps price attention, bonds
back honesty with equivocation locks ideally homed elsewhere with long unbonding
(whitepaper §9). Crucially, **a corrupt-quorum double-spend necessarily emits
equivocation proofs** (SPEC §7), so detection is automatic and needs no
governance. Detection is math; the *penalty* is a lock design, and that is where
it currently fails.

**Residual risk — High, because of a design flaw (BUG-6), before parameters even
matter.** The bond lock `any(all(sig(operator), after(unbond)), equivocation(w))`
pays whoever presents an equivocation proof, and **the first party to hold that
proof is the equivocator**: it signed both votes. So an operator equivocates and,
at once, spends its own bond to an address it controls through the equivocation
branch; the honest witnesses of the bond's home vote for the first valid request.
Reproduced: the claim is sealed by the bond home's honest quorum. The equivocation
branch is also not bound to the claimant (only `sig`/`multi` leaves sign the tid),
so any party that sees a bounty claim in flight, including the bond home's
witnesses, which see lock, salt and unlock in the SPEND request, can race it with
its own transition. That contradicts the whitepaper's "witnesses can't front-run
what they can't read": for non-signature branches, they can read it. The lock
language cannot constrain outputs, so whoever wins chooses where the bond goes.

Second, the **parameters are unspecified** (ROADMAP Phase 4:
"Stamp pricing and bond sizing" ⬜). Nothing today says how large a bond must be
relative to the value a constellation homes, or how stamps are priced against
spam cost. An AI adversary optimises against whatever numbers are chosen:
under-priced stamps → spam; under-sized bonds → profitable double-spend where
gain > slashed bonds; griefing where the attacker burns others' stamps / forces
recovery work for little cost.

**Mitigation:**
* **P1 (BUG-6):** never let the slashing branch be satisfied by the proof alone.
  Require a co-signature from parties independent of the operator, for example
  `all(equivocation(w), multi(k, auditors))` or a victims' / burn committee key,
  and give the operator branch a delay longer than the time to publish a proof.
  Longer term, a holder-checked covenant on the slashing branch (outputs must burn
  or pay a fixed pool). Until then, do not count bonds as a deterrent.
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
exploited the rotation seam specifically (fixed on main by seal settlement of
CONTESTED records, in both the Python and the newly ported Rust witness).

**Mitigation:** **P2** extend the rotation proof toward more versions, including the
new seal-settlement path; implement and model-check succession with partition
tolerance (whitepaper §10.4).

---

## 3. Findings

Every finding is a test in `tests/redteam/test_redteam.py` with a full
scenario / impact / suggested-fix docstring. The open ones are `expectedFailure`
tests that assert the property that *should* hold, and each was checked to fail for
its intended reason (not a setup error) on merged main `a22e412`. Nothing was fixed
in `sigil/`, per the task. `python3 -m unittest discover` stays green: 183 tests,
5 expected failures.

| # | Severity | Status on main | Where | One line | Test |
|---|---|---|---|---|---|
| BUG-1 | **Critical** (conservation / counterfeit) | **fixed** (every cached id reused is re-checked to hash to the presented entry) | `sigil/validate.py` `Verifier._verify` cache | A warm recipient's verifier cache skips re-validating a cached transition's body, so a malicious **payer** reuses a public ancestor tid (e.g. the genesis) with a forged body and an output minted from thin air; a 1000-supply asset inflated a recipient to ~1e9. Cold recipients reject. | `Finding1Conservation` |
| BUG-6 | **High** (economics: slashing void) | **open** (design) | bond lock pattern (whitepaper §7, SPEC §9); `locks.equivocation` | The equivocator holds its own equivocation proof first and claims its own bond; the claim is also front-runnable because the equivocation branch is not bound to the claimant. | `Finding6BondSelfClaim` |
| BUG-5 | Medium–High (protocol: swap hostage) | **open** | multi-party flow; `sigil/swap.py`, `Wallet.abort` | A counter-party binds only the honest input and vanishes; no death proof can exist and expiry does not release a bound input, so the honest coin is locked indefinitely. | `Finding5SwapHostage` |
| BUG-4 | Medium (policy evasion) | **fixed** (threshold on the payment total per asset; per-counter-party windows not done) | `sigil/wallet.py` `receive` | `deep_threshold` is applied per parcel, so splitting a payment into parcels just under it skips deep confirmation entirely. | `Finding4DeepConfirmSplit` |
| BUG-2 | Medium (liveness / third-party griefing) | **fixed** in `91269ff`/`eca6edd` | `wallet.py` rule-3 release + `deep_confirm`, `witness.py` ADOPT | A witness within *f* lying on STATUS induced an honest owner to bind twice; after rotation the honestly sealed coin was CONTESTED and deep confirmation failed for an innocent holder. Now settled by seal. | `Finding2InducedEquivocation` (regression) |
| BUG-3 | Low (robustness / contract) | **fixed** | `sigil/witness.py` `authorises` | A malformed non-dict `unlock` raises `AttributeError` (not caught) instead of `Rejected` from in-process `Witness.spend`; the HTTP server masks it as 400, no state mutated. | `Finding3MalformedLeak` |

**Also reproduced here and fixed on main by the parallel wallet work (`91269ff`):**
a payer overwriting the payee's own history through `Dossier.merge` of unverified
entries (the payee's coins became unprovable); the default trust policy accepting a
rogue home learned from the payer's dossier (double spend accepted by two payees);
and a parcel locked `any(sig(payee), sig(payer))` accepted as payment and then
clawed back. Each was re-run against main and now fails for the right reason.

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

Two long runs of `python -m tests.redteam.runner`, one before and one after merging
main (with `SIGIL_REDTEAM_BEYOND=1`):

| Engine / config | Before merge (`e02e82e`), 300 seeds × 200 steps | After merge (`a22e412`), 150 seeds × 200 steps | Violations |
|---|---|---|---|
| Explorer n = 4, b = f | 60 000 steps, 169 completions, 669 releases, 600 rotations | 30 000 steps, 95 completions, 346 releases, 300 rotations | none |
| Explorer n = 4, b = f, crash/restart via durable store | 60 000 steps, 39 completions, 334 releases, 539 rotations | 30 000 steps, 18 completions, 187 releases, 267 rotations | none |
| Explorer n = 7, b = f | 60 000 steps, 139 completions, 689 releases | 30 000 steps, 85 completions, 333 releases | none |
| Explorer n = 10, b = f | 60 000 steps, 121 completions, 688 releases | 30 000 steps, 64 completions, 489 releases | none |
| Explorer n = 4, **b = f+1** | S1 at seed 3 (613 steps) | S1 at seed 3 (613 steps) | **double spend, as expected** |
| Payment fuzzer (S3–S5) | 40 seeds: 2 185 payments, 363 swaps | 30 seeds: 1 638 payments, 280 swaps | none |
| Malformed-request leaks (BUG-3) | 1 888 | 897 | counted, not asserted |

In total: **360 000 adversarial witness-level steps and 4 466 wallet-level
operations with no safety violation within the fault bound.** The after-merge run
took 1 min 52 s on 4 cores; the default unittest run takes about 8 s.

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
4. **Liveness that depends on a counter-party.** A counter-party that binds the
   honest input and vanishes leaves no death proof (BUG-5); kill-switch inputs turn
   that hostage into a bounded free option, but cannot remove the option itself.
   And the whitepaper §10.7 split (equivocation plus witnesses unreachable forever)
   can still lock an honest input. An AI that owns network timing maximises both.
   A complete fix for the second is open.
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
where this review found a critical counterfeit (BUG-1), a slashing scheme the
cheater can defeat (BUG-6), a swap hostage (BUG-5), a way around deep confirmation
(BUG-4), a third-party griefing path (BUG-2, since fixed), and the measured
amplification and privacy gaps above. Sigil's design *minimises* the assumption
surface (no global state, no infrastructure that can steal, self-incriminating
cheating); it does not, and cannot, eliminate it.
