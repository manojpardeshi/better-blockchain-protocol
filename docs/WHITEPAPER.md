# Sigil: Value Without a Chain

*A design for moving value among people who don't trust each other, with no blocks, no chain, no global ordering, no global state, no miners or validators executing transactions, no gas, no mempool, and no native token.*

---

## 1. Start from the problem, not from Bitcoin

Every blockchain since 2009 answers the same question the same way:

> **Question:** how do people who don't trust each other stop someone from spending the same money twice?
>
> **Answer:** everybody keeps a copy of one ledger, and everybody agrees on the order of every entry in it.

Most of what makes blockchains slow, expensive, leaky and hard to scale follows from that answer, not from the question:

| Consequence of "one ordered ledger" | Why it hurts |
|---|---|
| Blocks and a chain | Batching for ordering puts a floor under latency (seconds to minutes) |
| Leader election (PoW / PoS lottery) | Burns energy or concentrates capital; leaders can censor |
| Global consensus | Every node waits on every other node; throughput is capped by the slowest |
| Global state | Every node stores and executes everything; costs grow with total use, not your use |
| Mempool and fee auctions | Users bid against each other for a scarce, ordered resource |
| MEV | Whoever orders the transactions can reorder them for profit |
| Probabilistic or delayed finality | "Final" means "probably won't be reorganised" |
| Public by default | Validators have to see a transaction to execute it |
| A single security assumption | One honest-majority assumption covers every asset and every user |

Sigil goes back to the question and gives a different answer.

## 2. The key observation: a double-spend is local

A double-spend is a conflict over **one specific coin**. It has nothing to do with any other coin in the world. Two payments by different people over different coins never conflict, so there is no reason to put them in order relative to each other.

What has to be guaranteed is **uniqueness**: each piece of value is consumed at most once. **Ordering** is not needed. Uniqueness is a far weaker requirement:

* **Total order** needs *consensus*. That is the expensive, leader-based, FLP-constrained machinery behind every chain.
* **Write-once uniqueness for an object with a single owner** needs only *quorum intersection*. If any two quorums of witnesses share an honest member, and honest witnesses never vote for two different spends of the same object, then two conflicting spends can't both collect a quorum.

The catch is that if an owner signs two conflicting spends at the same moment, the vote may split and *neither* spend gets a quorum. Consensus exists to break that tie. Sigil doesn't break it. **Only the owner can create the conflict, and the only person it hurts is the owner.** Honest owners never equivocate, so they never notice. Dropping the tie-breaker is what lets Sigil drop consensus entirely.

(The distributed-computing literature backs this up: asset transfer with single-owner accounts has consensus number 1. See §11.)

## 3. Five inversions

Sigil is what you get by inverting five things every chain assumes.

### Inversion 1: from order to uniqueness
No ledger, no blocks, no sequence numbers, no leader. A small group of **witnesses** attests one fact per coin: "this coin was consumed once, by this transition, with its owner's authorisation." Different coins are attested independently and in parallel, by different machines if needed, with no coordination between them.

### Inversion 2: from global state to carried proof
There is no world state. Your coin's validity travels with your coin as a **dossier**: the chain of transitions back to the coin's creation, plus the witness **seals** for each step. When you pay someone, you hand them the relevant part of your dossier. Nobody else stores your history, so nobody else has to.

### Inversion 3: from the network executing to the recipient validating
In a blockchain, validators run every transaction. In Sigil the work is split:

> **Witnesses enforce *who* and *once*. Holders enforce *what*.**

Witnesses check that the coin's owner authorised this specific transition (its **lock**) and that the coin wasn't already consumed. They never see asset types, amounts, recipients or the transaction graph. The **recipient** checks everything else: conservation of value, the asset's provenance, mint rules. The recipient is the one party with a real incentive to check, and they check only the history they're being asked to accept.

### Inversion 4: from one security assumption to a market of trust
Witnesses are organised into independent **constellations** (federations of *n* witnesses, tolerating *f* < *n*/3 faults). There is no "the network". Every coin names its **home** constellation, and every holder keeps a **trust policy** listing the constellations it accepts. Issuers, merchants and users choose; constellations compete on reputation, bonds, jurisdiction and price. Moving a coin from one constellation to another isn't a bridge. It's an ordinary payment whose output names a different home.

### Inversion 5: from auctioned blockspace to blind stamps
There is no blockspace, so there is nothing to auction and no MEV, because no one orders anything. Witnesses are paid with **stamps**: prepaid tokens issued with blind signatures, so a witness can't link a stamp to its buyer. Combined with witness blindness, a witness can't tell whose request it is serving or what it moves. It can serve everyone or go offline, but it can't discriminate.

## 4. The pieces

```
           ┌──────────────────── a transition ────────────────────┐
           │ header (what witnesses see)   │ body (what holders see)│
           │  inputs: [(sigil, gen), …]    │  inputs: [refs]        │
           │  body:   H(body)              │  outputs: [parcels]    │
           └───────────────────────────────┴────────────────────────┘
 parcel = {home, asset, amount, lock, salt}
 sigil  = H(home, lock, salt)          ← single-use; witnesses only see this
 tid    = H(header)
 vote   = Sign_witness(constellation, version, sigil, gen, tid, time)
 seal   = ≥ quorum matching votes      ← "sigil consumed by tid at gen"
```

* **Parcel**: a unit of value: which constellation it lives in, the asset, the amount, a **lock** (a small predicate saying who may spend it), and a random salt.
* **Sigil**: the parcel's single-use identifier, `H(home, lock, salt)`. It deliberately leaves out the asset and amount.
* **Lock / unlock**: a total, loop-free predicate language: `sig`, `multi` (k-of-n), `after`/`before` (time), `hash` (preimage), `equivocation` (anyone holding proof that a given witness cheated), `all`, `any`, `never`. Unlocks sign the pair *(sigil, transition id)*, so an authorisation can't be replayed into another transition.
* **Transition**: consumes parcels and creates parcels. Its id is the hash of a **header** listing input sigils (each with a *generation*) and the hash of the **body**. Witnesses receive only the header.
* **Witness**: signs a **vote** binding a sigil to one transition, at most once per generation.
* **Seal**: a quorum of matching votes. A transition is *complete* when every one of its inputs is sealed to it.
* **Dossier**: transitions, unlocks, seals and constellation charters, everything a holder needs to verify a parcel from its asset's genesis.
* **Charter**: a constellation's membership. Version 0's hash is the constellation id, and each later version is signed by a quorum of the previous one.
* **Asset**: created by a *genesis transition*. The asset id is that transition's id, so an asset can't be issued twice. Mintable supply is a **mint-right parcel** whose amount is the remaining cap. Conservation treats `asset` and `mint:asset` as one pool, and the mint right can only shrink.

## 5. Life of a payment

1. **Bob makes an address**: `{home, lock, salt}`. Bob picks the home constellation he trusts and a fresh one-time key.
2. **Alice builds a transition** consuming her parcels and creating Bob's parcel plus change.
3. **Alice signs** an unlock for each input over `(sigil, tid)`.
4. **Alice sends each input's header and unlock to that input's home witnesses.** Each witness checks the lock, checks it hasn't voted differently for this sigil at this generation, and returns a signed vote. One round trip; witnesses don't talk to each other.
5. **Alice collects a quorum of votes per input**, giving her seals. The transition is final. There are no confirmations to wait for and no reorganisations.
6. **Alice gives Bob the dossier** (the ancestry of his new parcel).
7. **Bob validates locally**: hashes, seals against charters he trusts, owners' unlocks, conservation, back to genesis. He caches what he has already verified, so each payment costs him only the history that is new to him.

## 6. Why it is safe

**Safety theorem.** If every constellation that sealed a parcel's history had fewer than a third Byzantine witnesses, then no sigil is consumed by two different complete transitions.

*Sketch (single charter version).* An honest witness votes at most once per *(sigil, generation)*. Any two quorums share at least one honest witness, so at a given generation at most one transition can be sealed for a sigil. Every transition header fixes the generation for each input, and an input only counts if it is sealed **at that generation**, so seals at other generations can't satisfy it.

Generations exist so honest parties can recover. Suppose Alice and Mallory sign an atomic swap, and Mallory secretly spends her own input elsewhere first. Alice's input is now bound to a transition that can never complete. Alice shows a **death proof**: either a seal binding one of the swap's inputs (at the generation the swap requires) to a *different* transition, or a quorum of votes for other transitions at that generation. Either way, quorum intersection means the swap can never be sealed. Witnesses then **release** Alice's sigil to the next generation, and she spends it again.

This is safe because a death proof is a timeless fact. Re-spending at generation *g*+1 needs a quorum at *g*+1, and that quorum shares an honest witness with any quorum that sealed generation *g*. That witness only moved past *g* after seeing proof that its generation-*g* transition is dead. So whatever the sigil was sealed to at *g* never completes.

**Rotation.** To change membership, old witnesses *freeze* (stop voting forever) and hand over evidence logs: owner-signed bindings and death-proof-backed releases. A quorum of them signs the new charter. Evidence can be checked without trusting the person handing it over, so a lying predecessor can hide evidence (the union of a quorum's logs covers that) but can't invent it. Every old seal shares an honest witness with the freezing quorum, so every sealed binding carries over. An owner who signed two live spends before rotation finds that sigil *contested* and frozen. Once again, only the equivocator loses.

These arguments are spelled out in [SPEC §8](SPEC.md#8-safety-argument). They are also tested in [`tests/test_model_check.py`](../tests/test_model_check.py), which runs the real witness code against an adversary that controls the owner and a Byzantine witness, and searches thousands of random schedules for a double-spend. A mutated witness that accepts bogus death proofs is caught within seconds.

## 7. What each adversary can and cannot do

| Adversary | Can | Cannot |
|---|---|---|
| A dishonest **owner** | Lock up their own parcel by equivocating | Hurt anyone else; honest co-signers recover through release |
| A dishonest **payer** | Send an invalid dossier | Get it accepted; the recipient validates |
| **< 1/3 of a constellation** | Refuse service; sign conflicting votes (which convicts them) | Block a spend, seal a double-spend, or see what moves |
| **≥ 1/3 of a constellation** (a corrupt quorum) | Seal a double-spend of a parcel whose owner equivocates with them, leaving signed **equivocation proofs** behind | **Steal** (holders re-check the owner's unlock), **inflate** (holders check conservation), or affect parcels homed elsewhere |
| A **network** attacker | Delay messages (liveness) | Break safety |
| **Retired witnesses** (long-range) | Forge seals for old history | Avoid producing equivocation proofs against bonds with long unbonding periods; fool holders who run deep confirmation against the current charter (see SPEC §9) |

Two of these properties have no equivalent in blockchains:

* **The infrastructure can't steal.** Even if every witness of a constellation is corrupt, it can't move a parcel without the owner's signature, because holders verify every unlock.
* **Cheating leaves evidence.** Witnesses never coordinate, so the only way to double-certify is for one witness to sign two conflicting votes, and a pair of signed votes is a self-contained proof. A witness's **bond** is just a parcel locked with `any(all(sig(operator), after(unbond_time)), equivocation(witness))`, so whoever holds the proof claims the bond. Slashing needs no chain, no governance and no court.

## 8. Properties

* **Finality:** deterministic, one round trip to the input's home witnesses. In the reference simulation a payment seals in a few milliseconds of compute.
* **Throughput:** no global bottleneck. Work per witness is one signature check and one record per spent sigil, with no ordering, no execution and no gossip. A witness can shard its sigil space across machines with no internal coordination, because sigils are independent. The system scales by adding constellations, and they need no coordination with each other.
* **Privacy:** witnesses see random-looking hashes. Asset, amount, sender and recipient appear only in bodies, which reach only later holders of the coin. The roadmap replaces full-ancestry dossiers with recursive succinct proofs (§10).
* **No MEV:** there is no ordering, so there is nothing to reorder. Witnesses can't front-run what they can't read.
* **Energy and hardware:** signature checks and a key-value store.
* **Interoperability:** a parcel's home is a per-parcel choice, so moving between constellations is an ordinary payment. An atomic swap across constellations is one transition whose inputs are sealed by both.
* **Upgradeability:** assets, conservation rules and dossier formats are client-side. Holders can adopt new rules without a fork, because there is no shared chain to fork.
* **No native token:** witnesses can sell stamps for any asset. Constellations compete on price, uptime and reputation.

## 9. Economics

* **Stamps** pay for attention. A witness sells blind-signed stamps in bulk, for any asset and through any channel, and redeems one per request. Spam costs stamps, and the witness learns nothing about who spends them.
* **Bonds** back honesty. An operator's stake sits in parcels with equivocation locks, ideally homed in a *different* constellation, with unbonding periods longer than their witnesses' terms.
* **Constellations compete.** Issuers choose a home for their genesis. Holders choose which homes to accept and can price risk, for example by asking for a stronger home on large payments. A merchant who doesn't trust Alice's constellation simply gives an address homed in one they do trust. The payment re-homes the value, and only the parcel's past seals have to be acceptable.

## 10. Limits and open problems

Sigil doesn't do everything a blockchain does, and this paper doesn't claim it does.

1. **Dossiers grow** with the history a coin has passed through. Mitigations: verifier caching (you pay only for history that is new to you); issuer *redemption* (an issuer can re-mint fresh parcels with short history); and, as the long-term answer, **recursive succinct proofs**, where each transition carries a constant-size proof that its whole ancestry is valid, which also hides that ancestry.
2. **Losing your dossier means losing your money**, just as losing your keys does. Wallets must back up dossiers (encrypted, anywhere: they are useless without the keys).
3. **Shared state** (an AMM pool, an auction, a DAO treasury) needs contention. Sigil's answer is to model the shared object as a parcel that is spent and re-created by each interaction. Interactions with that one object are sequential; the rest of the system stays parallel. Designing ergonomic *arbiter objects* is future work.
4. **Constellation death.** If a constellation disappears permanently, parcels homed there are stuck. Planned extension: charters name a *successor* that mirrors the evidence log and takes over after a dead-man period. Partition tolerance during takeover still needs work.
5. **Long-range forgery** by retired witnesses is visible (it produces equivocation proofs) but needs bonds with long unbonding and optional *deep confirmation* (asking the current charter whether old sigils are bound as the dossier claims).
6. **Witness clocks** are trusted for time-locks, but only to within the honest-quorum assumption. Each honest witness enforces time locally, so a seal shows that an honest quorum member saw the time.
7. **Pathological splits in multi-party transitions.** If a counter-party equivocates and the votes split *without* reaching a quorum on anything (some witnesses unreachable forever), a death proof may not exist and the honest party's input stays locked until those witnesses come back. Bonding counter-parties and retrying with fresh witnesses reduce this. A complete fix is open.
8. **Formal verification.** The safety argument is a proof sketch backed by randomised model checking. A TLA+ or Ivy proof is the next step.

## 11. Lineage

Sigil's building blocks have roots in research, and its contribution is how it combines them. Each idea below is credited to its source.

* *Single-use seals* (P. Todd) and *client-side validation* (RGB): value as seals that close once, validated by the holder.
* *Consensusless payments*: Guerraoui et al., "The Consensus Number of a Cryptocurrency" (2019); FastPay (2020); Astro (2020). These show that single-owner transfers need only Byzantine consistent broadcast.
* *Blind signatures*: Chaum (1982).

What is new in Sigil is the **removal of every global structure at the same time**. On top of that:

1. witnesses that enforce authorisation **blind** to value, using the header/body split;
2. **per-parcel homes**, which make cross-federation transfers and atomic swaps native, with no bridges;
3. **generations and death proofs**, which let honest parties recover inputs from failed multi-party transitions without consensus;
4. **evidence-carrying rotation**, so membership changes without a ledger;
5. **slashing as a lock predicate**, so penalties need no chain;
6. **per-holder trust policies** in place of a global security parameter;
7. **blind stamps**, so fees can't be used to censor.
