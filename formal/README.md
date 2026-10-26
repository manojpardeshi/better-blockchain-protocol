# Formal model of the Sigil witness protocol

`Sigil.tla` is a TLA+ specification of the witness protocol (docs/SPEC.md §3.9, §5.1, §5.2) over one or more constellations, including attacker-run ones. TLC machine-checks the §8 safety theorem against it, exhaustively, on small instances.

```
formal/check.sh              # all configs: 5 safety checks + 2 mutation tests, about 5 min on 4 cores
formal/check.sh MC.cfg       # one config
```

`check.sh` downloads `tla2tools.jar` v1.7.4 (an immutable release) into `~/.cache/sigil-tla/` (override with `TLA_CACHE`) and checks its SHA-256. It needs Java 11 or later and curl, and it uses the system CA bundle (TLS is always verified). The jar is never committed. CI runs the same script (job `formal` in `.github/workflows/test.yml`). Configs named `MC_multi*.cfg` are run against `MC_multi.tla`, the others against `MC.tla`.

## What is modelled

| Element | Model |
|---|---|
| Constellations | a set `Cons`. `Members[c]` is c's charter (one version, disjoint across constellations), `Quorum[c]` its q. Every witness is `Honest` or `Byz`. A constellation may be entirely Byzantine: a **rogue** constellation that the attacker created and that sits in the registry |
| Homes | `Home[s]` is a fixed constant. The sigil id commits to its home (§3.2), so nobody can make a sigil appear to have another home. Every home must satisfy the fault bound (`q = n − f`, at most f Byzantine members), as §8 assumes. Rogue constellations home no sigil of the model |
| Sigils / transitions | finite sets. `header[t]` is a non-empty set of `<<sigil, gen>>` with distinct sigils. A header may mix sigils of different homes. It is chosen in `Init` from `HeaderSpace` and stays fixed afterwards |
| Owners | fully adversarial. Every owner authorises every transition, so any spend request can reach any honest witness at any time, in any order |
| Honest record | `gen[w][s]`, `bound[w][s]` (Record.gen / Record.tid) |
| Votes | the tuple `<<c, w, s, g, t>>`, carrying its constellation c (w ∈ `Members[c]`), in a global, monotone set `votes`. It is public, as with STATUS (§5.3) |
| Seals | `SealedBy(c, s, g, t)`: ≥ `Quorum[c]` members of c voted. Any constellation, a rogue one included, can produce such a seal for any sigil. Holders accept only `Sealed(s, g, t) = SealedBy(Home[s], s, g, t)` (§6 rule 4), and *complete* is defined with it |
| `Spend(w,s,t)` | exactly §5.1 step 4, plus step 2: w serves only sigils homed at its own constellation. Stale `g < gen` is rejected; `g > gen` while bound is rejected; `g > gen` while unbound jumps and binds; `g = gen` while bound elsewhere is a Conflict; otherwise bind and vote. A rejection or Conflict changes no state, so it is modelled as the action being disabled |
| `Release(w,s)` | §5.2. It needs a bound tid and a **valid death proof** (§3.9) for that tid on **any** input `[s', g]` of its header (not necessarily `s`, and possibly homed at another constellation than w's). The proof is either kind `seal` (a seal for one other tid at `(s', g)`) or kind `votes` (≥ q distinct members of one constellation voting for other tids at `(s', g)`). **The seal or votes must come from `Home[s']`**: the fixed rule, where the proof carries the target's `{home, lock, salt}` and the witness checks `sigil_of(...) = s'` and the constellation. Byzantine votes count |
| Byzantine witnesses | sign any vote for themselves, under their own constellation, for any sigil, never for others (crypto is abstracted to unforgeability) |

**Mutation flags** (each must be caught by TLC):

* `AnyProof`: Release needs no death proof at all.
* `AnyConstellationProof`: a death proof's seal or votes may come from **any** constellation in the registry, not only from the home of the sigil it names. This is the behaviour of the implementation before the fix, and it allowed a real double spend (see below).

**Invariants checked:**

* `Safety` (the §8 theorem): for `t1 ≠ t2` that are both *complete* (every `[s,g]` in the header has a home seal for that tid at `g`), `SigilsOf(t1) ∩ SigilsOf(t2) = {}`.
* `HonestNoEquivocation`: an honest witness never votes for two tids at the same `(s, g)`, and only votes on sigils homed at its own constellation.
* `OneSealPerGen` (Lemma 1, home seals) and `DeathProofsSound` (Lemma 2: a transition with an acceptable death proof is never complete).
* `TypeOK`.

### Eager vs. lazy Byzantine votes

With `ByzEager = TRUE`, every vote a Byzantine witness could sign (rogue members included) exists from the initial state. This is the strongest adversary and is a sound reduction. `Spend` never reads `votes`, and the `Release` guard and `Complete` are monotone in `votes`. So every behaviour in which Byzantine votes are added lazily is matched step for step by the eager one, with a superset of votes, and any Safety violation carries over. `MC_lazy.cfg` cross-checks this: on a smaller instance, it runs the explicit `ByzVote` action, where Byzantine witnesses add votes one at a time.

## What is abstracted away

* **Cryptography:** hashes, Ed25519 and tids are replaced by identifiers, and signatures by "only `w` can create `w`'s vote". The binding of a sigil id to its home (`sigil = H(home, lock, salt)`) is the constant map `Home`.
* **Locks, unlocks, stamps and time:** §5.1 steps 1 and 3. The owner is adversarial and signs everything, so for safety these checks only remove behaviours.
* **Rotation:** FREEZE/ADOPT (§5.4), multiple charter versions and the contested state are not modelled. Each constellation has a single charter version.
* **Holder validation (§6):** conservation, the outputs and the body are not modelled. *Complete* is defined directly on home seals, as in §8.
* **Network:** messages are delivered atomically, as an honest witness's action. Loss, delay and reordering are covered because any action may fire at any time or never.
* **Bounded generations:** headers use `0..MaxGen`. A release at `MaxGen` moves to `MaxGen+1`, where nothing can bind any more.

## Instances and results

Single constellation: N = 4 (3 honest + 1 Byzantine), q = 3, so f = 1. Multi-constellation (`MC_multi.tla`): C = {h1, h2, h3, z1} (q = 3, f = 1), D = {h4} (q = 1, f = 0), and a rogue R = {r1}, all Byzantine, which can produce an R seal for any `(s, g, t)`. TLC v1.8.0 on 4 cores, Java 21, `-workers auto`:

| Config | Instance | Result | Distinct states | Generated | Depth | Time |
|---|---|---|---|---|---|---|
| `MC.cfg` | 3 sigils, 4 hand-picked transitions (`MC.tla`: same-generation conflict, multi-input death proof, release to generation 1, jump to generation 2), gens 0..2, eager Byzantine votes | **all invariants hold** | 46,932 | 609,739 | 21 | ~40 s |
| `MC_all.cfg` | 2 sigils, 3 transitions, **every** header assignment (15³ = 3375 maps), gens 0..2, eager Byzantine votes, symmetry on witnesses, sigils and tids | **all invariants hold** | 687,546 | 5,984,259 | 25 | ~175 s |
| `MC_lazy.cfg` | 2 sigils, 2 transitions, every header assignment, gens 0..1, **explicit `ByzVote`** | **all invariants hold** | 516,656 | 6,091,024 | 22 | ~60 s |
| `MC_mutant.cfg` | `MC.cfg` with `AnyProof = TRUE` (Release accepts any proof) | **Safety violated** (expected) | ~60–90k when found | ~0.4M | 8–10 | ~8 s |
| `MC_multi.cfg` | constellations C, D, R. The `MC.tla` transitions with a, b homed at C and c homed at D, so t3 and t4 span two constellations; gens 0..2, eager Byzantine votes (z1 and r1) | **all invariants hold** | 3,662 | 36,861 | 15 | ~5 s |
| `MC_multi_all.cfg` | constellations C, D, R; s1 homed at C, s2 at D, 3 transitions, **every** header assignment (3375 maps), gens 0..2, eager Byzantine votes, symmetry on C's honest witnesses and tids | **all invariants hold** | 60,240 | 363,168 | 17 | ~20 s |
| `MC_multi_mutant.cfg` | `MC_multi.cfg` with `AnyConstellationProof = TRUE` | **Safety violated** (expected) | ~8–9k when found | ~0.12M | 8–9 | ~4 s |

Times are from one `check.sh` run (5 min 11 s wall clock) on a loaded 4-core container. On the same machine the pre-constellation model needed ~130 s for `MC_all`, so the generalisation costs about 30% per state; state counts of the single-constellation configs are unchanged. A 3-sigil version of `MC_all` (gens 0..1, 26³ header maps) did not finish within 10 minutes, so it is not included. `MC_multi.cfg` has fewer states than `MC.cfg` because sigil c is served by a single witness. As a sanity check, temporary probe invariants confirmed that under the fixed rule the cross-constellation paths are live: h4 releases c at D using C's seal on `(b,0)` as death proof for t3, and t4 (a at C, c at D) can become complete.

### Mutation counterexample (`MC_mutant.cfg`)

TLC finds the following 7-step trace. z1 is Byzantine and has signed everything.

1. h1 and h2 vote `t2 = {(a,0)}`. With z1, `t2` is **complete**.
2. h3 jumps `a` to generation 1 and votes `t4 = {(a,1),(c,2)}`.
3. h1 and h2 jump `c` to generation 2 and vote `t4`. With z1, `(c,2)` is sealed for `t4`.
4. h1 **releases `a` without a valid proof** (the mutation): `t2` has no death proof, because it is sealed. h1 then votes `t4` at `(a,1)`.
5. `t4` is now complete as well, so sigil `a` is consumed by both `t2` and `t4`.

Under the real Release rule, step 4 is impossible: no death proof for `t2` can exist, because `(a,0)` has only z1 voting against `t2`. This is the honest-intersection argument of §8, case g₁ < g₂.

### Rogue-constellation counterexample (`MC_multi_mutant.cfg`)

This is the real double spend that the single-constellation model could not express. TLC finds a 6-step trace (the exact interleaving can vary between runs with several workers):

1. h1 and h2 vote `t2 = {(a,0)}` at C. With z1, `t2` is **completely sealed by a's home**.
2. h4 jumps `c` to generation 2 and votes `t4 = {(a,1),(c,2)}`. D's quorum is 1, so `(c,2)` is sealed for `t4`.
3. h3 jumps `a` to generation 1 and votes `t4`.
4. h1 **releases `a`**. The death proof it accepts names `(a,0)` and carries a seal for another tid (e.g. `t1`) on `(a,0)` **from the rogue constellation R**: r1 alone is R's quorum. That is a §3.6-valid seal, so a witness that accepts proofs from any constellation takes it.
5. h1 votes `t4` at `(a,1)`. With h3 and z1, `t4` is complete as well, so sigil `a` is consumed by both `t2` and `t4`.

With the fixed rule (`AnyConstellationProof = FALSE`), the proof in step 4 must be a seal or votes from C, a's home, and none exists (only z1 voted against `t2` at `(a,0)`). `MC_multi.cfg` and `MC_multi_all.cfg` check that no other path exists on those instances.

## Files

* `Sigil.tla`: the protocol, the invariants and the mutation flags.
* `MC.tla`: single-constellation instance definitions (fixed headers, all headers, symmetry sets).
* `MC_multi.tla`: multi-constellation instances (constellations C, D and the rogue R, homes).
* `MC.cfg`, `MC_all.cfg`, `MC_lazy.cfg`, `MC_mutant.cfg`, `MC_multi.cfg`, `MC_multi_all.cfg`, `MC_multi_mutant.cfg`: TLC configurations.
* `check.sh`: downloads TLC, runs the configs, and checks that the mutants fail and the others pass.
