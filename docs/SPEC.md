# Sigil Protocol Specification — v0 (draft)

The key words MUST, MUST NOT, SHOULD and MAY are used as in RFC 2119.
The reference implementation in [`sigil/`](../sigil) is authoritative where this text is ambiguous.

## 1. Roles

| Role | Holds | Does |
|---|---|---|
| **Holder** (wallet) | keys, parcels, dossiers, trust policy | builds and authorises transitions, gathers seals, validates received parcels |
| **Witness** | a signing key, a per-sigil record table | votes on spend requests, processes releases, hands over evidence on rotation |
| **Constellation** | a charter chain | groups *n* witnesses; tolerates *f* = ⌊(*n*−1)/3⌋ faults; quorum *q* = *n* − *f* |

There are no other roles. Witnesses never communicate with each other.

## 2. Conventions

* **Values** are JSON-native: objects, arrays, strings, integers, booleans, null. Byte strings are lowercase hex.
* **Canonical encoding** `enc(x)`: JSON, keys sorted, separators `,` and `:`, ASCII only, no NaN.
* **Hash** `H(tag, x)` = BLAKE2b-256(`"sigil/v0/" ‖ tag ‖ 0x00 ‖ enc(x)`), hex. Tags in use: `sigil`, `parcel`, `body`, `transition`, `charter`, `constellation`.
* **Signature** `Sig(sk, tag, x)` = Ed25519 over `"sigil/v0/sig/" ‖ tag ‖ 0x00 ‖ enc(x)`. Tags in use: `unlock`, `vote`, `charter`.
* **Amounts** are positive integers (booleans are not integers).

## 3. Objects

### 3.1 Parcel
```
parcel = {home: cid, asset: str, amount: int>0, lock: Lock, salt: str}
```
`home` is the id of the constellation that attests this parcel's sigil.

### 3.2 Sigil
```
sigil(p) = H("sigil", {home: p.home, lock: p.lock, salt: p.salt})
```
Wallets MUST use a fresh random salt (≥128 bits) for every receiving address.

### 3.3 References and assets
```
ref = {tx: tid, i: int}            parcel_id(ref) = H("parcel", ref)
```
Asset placeholders `""` (self) and `"mint:"` (self mint right) are legal only in genesis outputs. They resolve to `tid` and `"mint:" ‖ tid`. Any asset string starting with `"mint:"` is a **mint right** for the asset after the prefix.

### 3.4 Transition
```
body   = {inputs: [ref], outputs: [parcel], genesis: AssetCharter|null, memo: str}
header = {inputs: [[sigil, gen]], body: H("body", body)}
tid    = H("transition", header)
AssetCharter = {name: str, supply: int>0}
```
`header.inputs[k]` MUST correspond to `body.inputs[k]`. `gen` is the generation at which input *k* MUST be sealed.

### 3.5 Locks
```
Lock := {op:"sig",  pk}                 signature by pk
      | {op:"multi", k, pks}            k distinct signatures from pks (1 ≤ k ≤ |pks|, pks unique)
      | {op:"after", t} | {op:"before", t}   evaluator clock ≥ t  |  < t
      | {op:"hash", h}                  preimage x with BLAKE2b-256(x) = h
      | {op:"equivocation", witness}    a valid equivocation proof (§3.8) against witness
      | {op:"all", of:[Lock+]} | {op:"any", of:[Lock+]}
      | {op:"never"}
```
Objects MUST have exactly the listed keys. Depth ≤ 8, nodes ≤ 64, and at most 64 keys in all (`sig` keys plus every `multi` key list), so one evaluation checks at most 64 owner signatures. Evaluation is total and linear. An unlock carrying more than 64 equivocation proofs satisfies no lock: a lock has at most 64 nodes, so it never needs more, and the cap bounds the signature checks of one evaluation.

**Unlock** = `{sigs: {pk: sig}, preimages: {h: hex}, equivocations: [proof], expires: int}`. Signatures are `Sig(sk, "unlock", {sigil, tid, expires})`. `expires` is a time (seconds, same scale as `after`/`before`) chosen by the owner. It bounds when a witness may *newly* bind the sigil for this authorisation (§5.1), so an owner whose spend failed knows when no delayed request can still bind it (§4). All signatures in one unlock cover the same `expires`.

`eval(lock, unlock, sigil, tid, now)`: standard boolean semantics; signatures are checked over `{sigil, tid, unlock.expires}`, so changing `expires` invalidates them. When `now` is null (holder re-check), `after` and `before` evaluate to true. Holders do not check `expires` against any clock: once a binding exists, it may keep being voted and sealed after expiry.

### 3.6 Vote and seal
```
vote = {constellation, version, witness: pk, sigil, gen, tid, time, sig}
       sig = Sig(witness_sk, "vote", vote without sig)
seal = {constellation, version, sigil, gen, tid, votes: [{witness, time, sig}]}
```
A seal is **valid** for a registry *R* and convicted set *X* if, for charter `R[constellation][version]`, at least `q` distinct members not in *X* have valid votes. Each vote is rebuilt from the seal's own `constellation, version, sigil, gen, tid` plus the entry's `witness, time, sig`. Any other key in an entry is ignored and can never override a seal field.

### 3.7 Charter
```
charter_body = {name, version, witnesses: [pk], prev: H("charter", previous body) | null}
charter      = {body, sigs: {pk: Sig(sk, "charter", body)}}
cid          = H("constellation", body of version 0)
```
Version 0 needs no signatures. Version *v*+1 MUST be signed by a quorum of version *v*'s witnesses.

### 3.8 Equivocation proof
`{a: vote, b: vote}` where both votes are valid, `a.witness = b.witness`, `a.constellation = b.constellation`, `a.sigil = b.sigil`, `a.gen = b.gen`, and `a.tid ≠ b.tid`.

### 3.9 Death proof
A death proof for transition `(header, tid)` names an input `[s, g] ∈ header.inputs`, reveals that input's `parcel = {home, lock, salt}` with `sigil(parcel) = s`, and is one of:
* `{kind:"seal", sigil:s, gen:g, parcel, seal}`: a valid seal with `seal.sigil = s`, `seal.gen = g`, `seal.tid ≠ tid` and `seal.constellation = parcel.home`;
* `{kind:"votes", sigil:s, gen:g, parcel, votes}`: valid votes from at least `q` distinct members of one charter version of `parcel.home`, all with `sigil = s`, `gen = g`, `tid ≠ tid`.

The evidence MUST come from the target sigil's home. Constellations are permissionless, so a seal from any other constellation proves nothing about `s`; since the sigil commits to its home (§3.2), the home cannot be misstated.

### 3.10 Stamp
`{serial: hex, sig: hex}`, an RSA-FDH signature over `serial` by the witness's stamp key. The witness obtains it by blind-signing `FDH(serial)·rᵉ mod N`. Each serial is redeemable once.

### 3.11 Dossier
```
{transitions: {tid: {header, body, unlocks: {sigil: Unlock}}},
 seals:       {"sigil:tid": seal},
 charters:    {cid: [charter]}}
```

## 4. Holder obligations

1. A holder MUST NOT authorise two different transitions that consume the same sigil at the same generation, except after releasing a pledge under rule 3. Re-authorising the *same* transition (for example with a later `expires`) is allowed; it is not equivocation.
2. A holder MUST NOT authorise a transition at generation *g*+1 for a sigil until it holds a valid death proof (§3.9) for the transition it pledged at *g*. That transition can then never be sealed (§8 Lemma 2), so no second binding at *g* can follow; witnesses still bound to it at *g* are released with the same proof, and unbound ones accept *g*+1 directly (§5.1 step 6).
3. **Pledge release.** An authorisation of `(s, g, T)` that the holder failed to seal (a *pledge*) may be released, and a different transition of `s` at `g` authorised, only when both hold:
   * *expiry:* by the holder's clock, `now > E + skew`, where `E` is the latest `expires` it ever signed for `(s, g, T)` and `skew` bounds how far any honest witness's clock may lag the holder's (v0 default: 120 s). Then no honest witness will newly bind `s` to `T` (§5.1), however late a request arrives;
   * *no binding:* every member of the home's current charter answered STATUS, and none reports a binding to, or a vote for, `T` at `g`. An unreachable member might hold one.

   Without the expiry condition, a request delayed in flight could bind `s` to `T` after the holder checked, and the holder would then authorise two transitions (rule 1). If a binding exists, the pledge stays: the holder may still complete `T` (re-authorising it with a fresh `expires`) or recover via a death proof (§5.2).
4. Receiving addresses MUST use fresh salts. A recipient SHOULD check that the received sigil is unbound at its home (at most *f* witnesses report a binding).
5. A holder SHOULD keep verified-transition caches and MUST clear them when its trust policy changes.
6. **What a holder signs.** Before authorising, a holder MUST check that `header.body = H("body", body)`, that header and body list the same number of inputs, and that each of its own inputs appears at its own position with its own sigil and its current generation. It MUST NOT authorise while a live pledge of that sigil names another transition (at any generation), and SHOULD first ask the home's witnesses: if any reports a binding or vote at that generation for a transition it has no pledge for (a pledge lost in a crash), it MUST NOT authorise.
7. **What a holder accepts.** A recipient MUST accept a parcel only at an address it issued, exactly (`home`, `lock` and `salt`): a lock that merely includes the recipient's key may still be spendable by the payer. It MUST NOT credit two parcels with one sigil. Its trust policy is its own: charters a received dossier introduces are learned (to verify seals) but never trusted unless the owner adds them, and the policy MUST survive a restart.
8. **Durability.** A holder MUST make every pledge, and the header and body it authorised, durable before any witness sees the authorisation. After expiry a pledge that bound nothing is released (rule 3); otherwise the holder completes the transition (re-authorising the same tid, rule 1) or aborts it with a death proof (rule 2).

## 5. Witness protocol

Per sigil, a witness stores `Record{gen=0, tid=null, header=null, vote=null, log=[], votes=[]}`.

A witness MUST make its records (and its frozen flag) durable before it releases a SPEND vote, a RELEASE result or a FREEZE response, so that a crash and restart can never lead it to vote twice at one `(sigil, gen)`.

### 5.1 SPEND(req)
`req = {sigil, header, home, lock, salt, unlock, stamp?}`

1. If inactive or frozen → reject. If stamps are required and `stamp` is missing, invalid or already redeemed → reject; otherwise redeem it.
2. `home` MUST equal this constellation's id.
3. **Authorisation:** `sigil({home, lock, salt}) = sigil`; `sigil` occurs exactly once in `header.inputs` with generation `g` (a non-negative integer); all header sigils are distinct; `unlock.expires` is an integer; `tid = H("transition", header)`; `eval(lock, unlock, sigil, tid, now)` holds with the witness's clock.
4. Let `r` = record(sigil).
   * `g < r.gen` → reject (stale).
   * `g > r.gen`: if `r.tid ≠ null` → reject (release first). Otherwise set `r.gen = g`. Skipping generations without voting is abstention and is safe.
   * If `r.tid = null`: if `now > unlock.expires` by the witness's clock → reject (authorisation expired); a witness MUST NOT newly bind a sigil on an expired authorisation. Otherwise bind `r.tid = tid`, `r.header = header`, append `{kind:"bind", gen:g, auth:{home, lock, salt, unlock, header}}` to `r.log`.
   * If `r.tid ≠ tid` → reply **Conflict** carrying the existing vote.
   * Otherwise return `r.vote`, creating and recording it on first use. (Re-voting an existing binding is allowed after expiry.)

A witness MUST NOT sign two votes with the same `(constellation, sigil, gen)` and different `tid`.

### 5.2 RELEASE(sigil, proof)
1. `r` = record(sigil). Require `r.tid` to be a transition or contested (not null).
2. If `r` is contested: require `proof` to be a valid death proof for at least one of `r.candidates` (§5.4). For each candidate `(g, tid, header)` it kills, append a `release` entry for it to `r.log`, remove it, and set `r.gen = max(r.gen, g+1)`. Once no candidate is left, clear `tid` and raise `r.gen` past every generation of the witness's own votes. Stop here.
3. Otherwise require `proof` to be a valid death proof for `(r.header, r.tid)` (§3.9).
4. Append `{kind:"release", gen:r.gen, tid:r.tid, header:r.header, proof}` to `r.log`, then set `r.gen += 1` and clear `tid`, `header`, `vote` and `abstain`.

### 5.3 STATUS(sigil)
Return `{gen, tid, votes}`. `votes` is every vote this witness ever cast on the sigil. Anyone may query. It is used for death proofs and freshness checks.

### 5.4 FREEZE(next_charter) / ADOPT
* FREEZE: require `next_charter.prev = H("charter", current body)`. A witness freezes for exactly one successor: if already frozen for a different `next_charter`, reject. Persist `H("charter", next_charter)` and set frozen (no further votes or releases, ever). Return a signature on `next_charter` and the evidence `{sigil: log ‖ [{kind:"vote", vote} for every vote this witness cast on sigil]}`.
* The new charter is valid once a quorum of current members have signed it.
* A member of version *v* > 0 MUST enter it by ADOPT, never by joining bare; only version 0 has no predecessors to inherit from. Over the wire (WIRE.md "Rotation") FREEZE and ADOPT are operator calls, since anyone able to send FREEZE could halt a witness for good.
* ADOPT(snapshots), run by each member of the new version. For each sigil, collect the union of log entries from all snapshots (a snapshot that is not an object, a log that is not a list and an entry that is not an object are skipped: like any unverifiable evidence, they count as omitted), then:
  * keep `bind` entries whose `auth` passes §5.1 step 3 with `now = null`; each gives a pair `(g, tid)`;
  * collect `dead` = the tids of `release` entries whose death proof verifies against their stated header;
  * `alive` = kept bindings whose tid is not in `dead`;
  * `own` = the adopter's own earlier votes on the sigil: valid `vote` entries signed by its own key for this constellation, plus any it already holds (a re-used key MUST bring its own votes);
  * exactly one alive `(g, tid)`, and no other kept binding at `g` → record `gen = g`, bound to `tid`; if `own` holds a vote at `g` for another tid, mark the record **abstain**: it never votes at `g` (a release still moves it on);
  * otherwise, if any binding is alive → record **contested** with `candidates` = the alive `(g, tid, header)`, at `gen = max over kept bindings of (g+1 if dead else g)`. A contested record rejects all spends; RELEASE removes candidates as they are proven dead (§5.2). Two tids bound at one generation mean the owner equivocated there, and the evidence cannot show which one (if either) a quorum sealed. Inheriting the surviving one could seal a second tid at a generation whose sealed tid was later released;
  * none → record unbound at `gen = max over kept bindings of (g+1 if dead else g)`, raised to one past the highest generation in `own`, or 0.

  A witness therefore never signs two tids for one `(constellation, sigil, gen)`, even across charter versions, so §3.8 equivocation proofs cannot be manufactured against an honest key.

## 6. Holder validation

`verify(dossier, ref)`: verify each charter chain (§3.7), then verify `ref.tx` and, recursively, its ancestors (memoised). A transition `tid` is valid if and only if:

1. `H("transition", header) = tid` and `H("body", body) = header.body`.
2. Outputs are non-empty and every output is a well-formed parcel (exact keys, amount > 0, well-formed lock).
3. **Genesis** (`body.genesis ≠ null`): no inputs; outputs use only `""` or `"mint:"` assets; the sum of output amounts equals `genesis.supply`.
4. **Spend**: inputs are non-empty; `|body.inputs| = |header.inputs|`; input refs are distinct; header sigils are distinct; and for each *k*:
   * `p` = resolved output at `body.inputs[k]` (its transition is valid), and `sigil(p) = header.inputs[k][0]`;
   * `seal = dossier.seals[sigil:tid]` exists, with `seal.gen = header.inputs[k][1]` and `seal.constellation = p.home`;
   * the holder's policy trusts `p.home`, and the seal is valid (§3.6) with convicted witnesses excluded;
   * `eval(p.lock, unlocks[sigil], sigil, tid, null)` holds.
5. **Conservation**: outputs contain no placeholder assets. For every base asset *X*, `in(X) + in(mint:X) = out(X) + out(mint:X)` and `out(mint:X) ≤ in(mint:X)`.

To accept a received parcel, the holder MUST also trust its `home`.

## 7. Parameters (v0)

| Parameter | Value |
|---|---|
| Hash | BLAKE2b-256 |
| Signatures | Ed25519 |
| Stamp signatures | RSA-FDH, ≥ 2048-bit modulus (1024 allowed only in tests) |
| Fault bound | *f* = ⌊(*n*−1)/3⌋, *q* = *n* − *f* |
| Lock limits | depth 8, 64 nodes, 64 keys |
| Authorisation lifetime (wallet default) | `expires` = now + 600 s |
| Clock-skew margin for pledge release (wallet default) | 120 s |

## 8. Safety argument

**Definitions.** A transition `T` is *complete* if, for every `[s, g] ∈ T.header.inputs`, a valid seal for `(s, g, T)` exists. Assume each constellation version has at most *f* Byzantine members, and let *n* > 3*f*.

**Lemma 1 (one seal per generation).** For fixed `(s, g)` and charter version, at most one tid has a valid seal. *Proof:* two seals need 2*q* votes among *n* witnesses, so they share at least 2*q* − *n* ≥ *f*+1 witnesses, at least one of them honest. An honest witness votes at most once per `(s, g)` (§5.1).

**Lemma 2 (death proofs are sound).** If a valid death proof exists for `T` on input `(s, g)`, then no valid seal for `(s, g, T)` ever exists. *Proof:* The proof's evidence is from `s`'s home (§3.9), the only constellation whose seals count for `s`. (seal kind) by Lemma 1. (votes kind) *q* votes for other tids include at least *q* − *f* honest witnesses who will never vote `T` at `(s, g)`, so `T` can get at most *n* − (*q* − *f*) = 2*f* < *q* votes. ∎ Because a header fixes `g`, seals for `s` at other generations don't count toward `T`.

**Theorem (no double consumption).** No sigil `s` is an input of two different complete transitions. *Proof sketch:* suppose `T₁` needs `(s, g₁)` and `T₂` needs `(s, g₂)`, and both are complete.
*Case g₁ = g₂:* contradicts Lemma 1.
*Case g₁ < g₂:* the seal for `(s, g₂, T₂)` has at least *f*+1 honest voters, and so does the seal for `(s, g₁, T₁)`. These two honest sets have sizes adding up to more than the *n* − *f* honest witnesses, so some honest witness *w* is in both. *w* voted `T₁` at `g₁` and later voted at `g₂ > g₁`. Since *w* was bound at `g₁`, it could only advance by RELEASE, which required a valid death proof for `T₁`. By Lemma 2, `T₁` is not complete. Contradiction. ∎

**Rotation.** Every seal of version *v* shares at least one honest witness with the quorum *F* that froze and signed version *v*+1, and that witness's log contains the binding (with the owner's authorisation, which successors can verify). After freezing, at most *f* honest members of *v* are unfrozen, which is fewer than the *q* − *f* honest votes a new seal needs, so no new seal of version *v* can form. ADOPT therefore keeps every sealed binding as alive (or dead with proof). If a sealed binding `(g, u)` is alive, the new version either binds `u` at `g` or is contested with `u` as a candidate, and leaves `g` only once `u` is proven dead. If `u` is dead, `(g, u)` is still in the evidence, so an alive sibling at `g` makes the record contested and otherwise the record is unbound past `g`. Either way the new version never votes a second tid at `g`. This rule is model-checked in `formal/MC_rot_sibling*.cfg`. The **contested** state only arises when an owner authorised two transitions at one generation.

**Holders cannot be robbed by witnesses.** Rule 6.4 re-checks the owner's unlock, so even a seal produced by a fully corrupt quorum can't spend a parcel without its lock's signatures. Witnesses enforce time locks; holders accept time conditions on the quorum's word.

**Mechanised check.** `tests/test_model_check.py` explores adversarial schedules against the real witness code. The adversary controls the owner and a Byzantine witness that signs anything and joins every seal and death proof. As a mutation test, it confirms that a witness accepting any death proof is caught. `tests/test_model_check_extended.py` extends the exploration to charter rotations (adversarial signing quorums, unfrozen ex-members, forged snapshots from a Byzantine signer, a Byzantine member in every version, seals counted from any version) and to transitions spanning two constellations, each with its own mutation tests. [`formal/Sigil.tla`](../formal) is a TLA+ model of §5.1–5.2 and §3.9 over several constellations, including an all-Byzantine one controlled by the attacker, and TLC checks the theorem and both lemmas against it exhaustively on small instances (see `formal/README.md`). Its mutation tests include accepting death proofs from any constellation rather than the named sigil's home, which TLC catches as a double spend.

**Fixed gaps.** The extended model checker found two issues in v0, both now fixed and covered by `KnownGapTests` in `tests/test_model_check_extended.py` (regression tests): (1) death proofs were not bound to the target sigil's home, so a seal from an attacker-run constellation could release a sealed transition and allow a double spend; §3.9 now requires the evidence to come from the home. (2) ADOPT could make a re-used honest key sign two tids for the same `(constellation, sigil, gen)`, a valid §3.8 equivocation proof against an honest witness; ADOPT now honours the key's own earlier votes (§5.4). The explorer treats an honest key's equivocation as a violation. The TLA+ model covers the first: with death proofs restricted to the named sigil's home it finds no violation, and without that restriction it finds the double spend. It has no rotation, so it does not cover the second.

## 9. Recommended policies (non-normative)

* **Deep confirmation.** Seals remain valid after their charter retires, so retired witness keys colluding with an owner could forge a seal for a sigil really consumed elsewhere (a long-range forgery). For high-value receipts, for every consumed input `[s, g]` of every transition `tid` in the received parcel's ancestry, query STATUS(s) at the *current* charter of `s`'s home and require at least *f*+1 current members to report `gen = g` and `tid` bound. With at most *f* faulty current members, at least one honest witness then vouches for the binding, and honest witnesses inherit every real binding on rotation (§5.4), so a forgery fails. Wallets cache confirmed `(s, g, tid)` triples. The reference wallet runs it for receipts at or above a configurable `deep_threshold`.
* **Bond homes.** Home witness bonds in a constellation other than the witness's own, with unbonding longer than the witness's term plus the deep-confirmation horizon.
* **Payment size.** Accept large payments only into homes with larger *n* and stronger bonds.

## 10. Extensions under design

* **Succession:** a charter names a successor that mirrors evidence logs and adopts after a dead-man period.
* **Recursive proofs:** replace dossiers with constant-size proofs of ancestry validity.
* **Arbiter objects:** conventions for shared state as sequentially re-created parcels.
* **Transport:** a request/response wire protocol (this draft defines messages, not transport).
