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
Objects MUST have exactly the listed keys. Depth ≤ 8, nodes ≤ 64. Evaluation is total and linear.

**Unlock** = `{sigs: {pk: sig}, preimages: {h: hex}, equivocations: [proof]}`. Signatures are `Sig(sk, "unlock", {sigil, tid})`.

`eval(lock, unlock, sigil, tid, now)`: standard boolean semantics. When `now` is null (holder re-check), `after` and `before` evaluate to true.

### 3.6 Vote and seal
```
vote = {constellation, version, witness: pk, sigil, gen, tid, time, sig}
       sig = Sig(witness_sk, "vote", vote without sig)
seal = {constellation, version, sigil, gen, tid, votes: [{witness, time, sig}]}
```
A seal is **valid** for a registry *R* and convicted set *X* if, for charter `R[constellation][version]`, at least `q` distinct members not in *X* have valid votes.

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
A death proof for transition `(header, tid)` names an input `[s, g] ∈ header.inputs` and is one of:
* `{kind:"seal", sigil:s, gen:g, seal}`: a valid seal with `seal.sigil = s`, `seal.gen = g`, `seal.tid ≠ tid`;
* `{kind:"votes", sigil:s, gen:g, votes}`: valid votes from at least `q` distinct members of one charter version, all with `sigil = s`, `gen = g`, `tid ≠ tid`.

### 3.10 Stamp
`{serial: hex, sig: hex}`, an RSA-FDH signature over `serial` by the witness's stamp key. The witness obtains it by blind-signing `FDH(serial)·rᵉ mod N`. Each serial is redeemable once.

### 3.11 Dossier
```
{transitions: {tid: {header, body, unlocks: {sigil: Unlock}}},
 seals:       {"sigil:tid": seal},
 charters:    {cid: [charter]}}
```

## 4. Holder obligations

1. A holder MUST NOT authorise two different transitions that consume the same sigil at the same generation.
2. A holder MUST NOT authorise a transition at generation *g*+1 for a sigil until a quorum of its home has released generation *g*.
3. Receiving addresses MUST use fresh salts. A recipient SHOULD check that the received sigil is unbound at its home (at most *f* witnesses report a binding).
4. A holder SHOULD keep verified-transition caches and MUST clear them when its trust policy changes.

## 5. Witness protocol

Per sigil, a witness stores `Record{gen=0, tid=null, header=null, vote=null, log=[], votes=[]}`.

### 5.1 SPEND(req)
`req = {sigil, header, home, lock, salt, unlock, stamp?}`

1. If inactive or frozen → reject. If stamps are required and `stamp` is missing, invalid or already redeemed → reject; otherwise redeem it.
2. `home` MUST equal this constellation's id.
3. **Authorisation:** `sigil({home, lock, salt}) = sigil`; `sigil` occurs exactly once in `header.inputs` with generation `g` (a non-negative integer); all header sigils are distinct; `tid = H("transition", header)`; `eval(lock, unlock, sigil, tid, now)` holds with the witness's clock.
4. Let `r` = record(sigil).
   * `g < r.gen` → reject (stale).
   * `g > r.gen`: if `r.tid ≠ null` → reject (release first). Otherwise set `r.gen = g`. Skipping generations without voting is abstention and is safe.
   * If `r.tid = null`: bind `r.tid = tid`, `r.header = header`, append `{kind:"bind", gen:g, auth:{home, lock, salt, unlock, header}}` to `r.log`.
   * If `r.tid ≠ tid` → reply **Conflict** carrying the existing vote.
   * Otherwise return `r.vote`, creating and recording it on first use.

A witness MUST NOT sign two votes with the same `(constellation, sigil, gen)` and different `tid`.

### 5.2 RELEASE(sigil, proof)
1. `r` = record(sigil). Require `r.tid` to be a transition (not null, not contested).
2. Require `proof` to be a valid death proof for `(r.header, r.tid)` (§3.9).
3. Append `{kind:"release", gen:r.gen, tid:r.tid, header:r.header, proof}` to `r.log`, then set `r.gen += 1` and clear `tid`, `header` and `vote`.

### 5.3 STATUS(sigil)
Return `{gen, tid, votes}`. `votes` is every vote this witness ever cast on the sigil. Anyone may query. It is used for death proofs and freshness checks.

### 5.4 FREEZE(next_charter) / ADOPT
* FREEZE: require `next_charter.prev = H("charter", current body)`. Set frozen (no further votes or releases, ever). Return a signature on `next_charter` and the evidence `{sigil: log}`.
* The new charter is valid once a quorum of current members have signed it.
* ADOPT(snapshots), run by each member of the new version. For each sigil, collect the union of log entries from all snapshots, then:
  * keep `bind` entries whose `auth` passes §5.1 step 3 with `now = null`; each gives a pair `(g, tid)`;
  * collect `dead` = the tids of `release` entries whose death proof verifies against their stated header;
  * `alive` = kept bindings whose tid is not in `dead`;
  * exactly one alive `(g, tid)` → record `gen = g`, bound to `tid`;
  * more than one → record **contested** (rejects all spends and releases);
  * none → record unbound at `gen = max over kept bindings of (g+1 if dead else g)`, or 0.

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
| Lock limits | depth 8, 64 nodes |

## 8. Safety argument

**Definitions.** A transition `T` is *complete* if, for every `[s, g] ∈ T.header.inputs`, a valid seal for `(s, g, T)` exists. Assume each constellation version has at most *f* Byzantine members, and let *n* > 3*f*.

**Lemma 1 (one seal per generation).** For fixed `(s, g)` and charter version, at most one tid has a valid seal. *Proof:* two seals need 2*q* votes among *n* witnesses, so they share at least 2*q* − *n* ≥ *f*+1 witnesses, at least one of them honest. An honest witness votes at most once per `(s, g)` (§5.1).

**Lemma 2 (death proofs are sound).** If a valid death proof exists for `T` on input `(s, g)`, then no valid seal for `(s, g, T)` ever exists. *Proof:* (seal kind) by Lemma 1. (votes kind) *q* votes for other tids include at least *q* − *f* honest witnesses who will never vote `T` at `(s, g)`, so `T` can get at most *n* − (*q* − *f*) = 2*f* < *q* votes. ∎ Because a header fixes `g`, seals for `s` at other generations don't count toward `T`.

**Theorem (no double consumption).** No sigil `s` is an input of two different complete transitions. *Proof sketch:* suppose `T₁` needs `(s, g₁)` and `T₂` needs `(s, g₂)`, and both are complete.
*Case g₁ = g₂:* contradicts Lemma 1.
*Case g₁ < g₂:* the seal for `(s, g₂, T₂)` has at least *f*+1 honest voters, and so does the seal for `(s, g₁, T₁)`. These two honest sets have sizes adding up to more than the *n* − *f* honest witnesses, so some honest witness *w* is in both. *w* voted `T₁` at `g₁` and later voted at `g₂ > g₁`. Since *w* was bound at `g₁`, it could only advance by RELEASE, which required a valid death proof for `T₁`. By Lemma 2, `T₁` is not complete. Contradiction. ∎

**Rotation.** Every seal of version *v* shares at least one honest witness with the quorum *F* that froze and signed version *v*+1, and that witness's log contains the binding (with the owner's authorisation, which successors can verify). After freezing, at most *f* honest members of *v* are unfrozen, which is fewer than the *q* − *f* honest votes a new seal needs, so no new seal of version *v* can form. ADOPT therefore keeps every sealed binding as alive (or dead with proof). The **contested** state only arises when an owner authorised two transitions that were never proven dead.

**Holders cannot be robbed by witnesses.** Rule 6.4 re-checks the owner's unlock, so even a seal produced by a fully corrupt quorum can't spend a parcel without its lock's signatures. Witnesses enforce time locks; holders accept time conditions on the quorum's word.

**Mechanised check.** `tests/test_model_check.py` explores adversarial schedules against the real witness code. The adversary controls the owner and a Byzantine witness that signs anything and joins every seal and death proof. As a mutation test, it confirms that a witness accepting any death proof is caught.

## 9. Recommended policies (non-normative)

* **Deep confirmation.** For high-value receipts, query the current charter's STATUS for each sigil in the dossier and require each to be bound to the claimed tid. This detects long-range forgery by retired witnesses.
* **Bond homes.** Home witness bonds in a constellation other than the witness's own, with unbonding longer than the witness's term plus the deep-confirmation horizon.
* **Payment size.** Accept large payments only into homes with larger *n* and stronger bonds.

## 10. Extensions under design

* **Succession:** a charter names a successor that mirrors evidence logs and adopts after a dead-man period.
* **Recursive proofs:** replace dossiers with constant-size proofs of ancestry validity.
* **Arbiter objects:** conventions for shared state as sequentially re-created parcels.
* **Transport:** a request/response wire protocol (this draft defines messages, not transport).
