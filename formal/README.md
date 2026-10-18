# Formal model of the Sigil witness protocol

`Sigil.tla` is a TLA+ specification of the witness protocol (docs/SPEC.md §3.9, §5.1, §5.2). TLC machine-checks the §8 safety theorem against it, exhaustively, on small instances.

```
formal/check.sh              # all configs: 3 safety checks + 1 mutation test, about 2.5 min on 4 cores
formal/check.sh MC.cfg       # one config
```

`check.sh` downloads `tla2tools.jar` v1.8.0 into `~/.cache/sigil-tla/` (override with `TLA_CACHE`) and checks its SHA-256. It needs Java 11 or later and curl, and it uses the system CA bundle (TLS is always verified). The jar is never committed. CI runs the same script (job `formal` in `.github/workflows/test.yml`).

## What is modelled

| Element | Model |
|---|---|
| Witnesses | `Honest ∪ Byz`, one constellation version, quorum `Quorum` |
| Sigils / transitions | finite sets. `header[t]` is a non-empty set of `<<sigil, gen>>` with distinct sigils. It is chosen in `Init` from `HeaderSpace` and stays fixed afterwards |
| Owners | fully adversarial. Every owner authorises every transition, so any spend request can reach any honest witness at any time, in any order |
| Honest record | `gen[w][s]`, `bound[w][s]` (Record.gen / Record.tid) |
| Votes | the tuple `<<w, s, g, t>>` in a global, monotone set `votes`. It is public, as with STATUS (§5.3) |
| `Spend(w,s,t)` | exactly §5.1 step 4: stale `g < gen` is rejected; `g > gen` while bound is rejected; `g > gen` while unbound jumps and binds; `g = gen` while bound elsewhere is a Conflict; otherwise bind and vote. A rejection or Conflict changes no state, so it is modelled as the action being disabled |
| `Release(w,s)` | §5.2. It needs a bound tid and a **valid death proof** (§3.9) for that tid on **any** input `[s', g]` of its header (not necessarily `s`). The proof is either kind `seal` (≥ q votes for one other tid at `(s', g)`) or kind `votes` (≥ q distinct witnesses voting for other tids at `(s', g)`). Byzantine votes count |
| Byzantine witnesses | sign any vote for themselves, never for others (crypto is abstracted to unforgeability) |

**Invariants checked:**

* `Safety` (the §8 theorem): for `t1 ≠ t2` that are both *complete* (every `[s,g]` in the header has ≥ q votes for that tid at `g`), `SigilsOf(t1) ∩ SigilsOf(t2) = {}`.
* `HonestNoEquivocation`: an honest witness never votes for two tids at the same `(s, g)`.
* `OneSealPerGen` (Lemma 1) and `DeathProofsSound` (Lemma 2: a transition with a death proof is never complete).
* `TypeOK`.

### Eager vs. lazy Byzantine votes

With `ByzEager = TRUE`, every vote a Byzantine witness could sign exists from the initial state. This is the strongest adversary and is a sound reduction. `Spend` never reads `votes`, and the `Release` guard and `Complete` are monotone in `votes`. So every behaviour in which Byzantine votes are added lazily is matched step for step by the eager one, with a superset of votes, and any Safety violation carries over. `MC_lazy.cfg` cross-checks this: on a smaller instance, it runs the explicit `ByzVote` action, where Byzantine witnesses add votes one at a time.

## What is abstracted away

* **Cryptography:** hashes, Ed25519 and tids are replaced by identifiers, and signatures by "only `w` can create `w`'s vote".
* **Locks, unlocks, stamps, the home check and time:** §5.1 steps 1 to 3. The owner is adversarial and signs everything, so for safety these checks only remove behaviours.
* **Rotation:** FREEZE/ADOPT (§5.4), charters, multiple constellation versions and the contested state are not modelled. The model has a single charter version.
* **Holder validation (§6):** conservation, the outputs and the body are not modelled. *Complete* is defined directly on votes, as in §8.
* **Network:** messages are delivered atomically, as an honest witness's action. Loss, delay and reordering are covered because any action may fire at any time or never.
* **Bounded generations:** headers use `0..MaxGen`. A release at `MaxGen` moves to `MaxGen+1`, where nothing can bind any more.

## Instances and results

N = 4 (3 honest + 1 Byzantine), q = 3, so f = 1. TLC v1.8.0 on 4 cores, Java 21, `-workers auto`:

| Config | Instance | Result | Distinct states | Generated | Depth | Time |
|---|---|---|---|---|---|---|
| `MC.cfg` | 3 sigils, 4 hand-picked transitions (`MC.tla`: same-generation conflict, multi-input death proof, release to generation 1, jump to generation 2), gens 0..2, eager Byzantine votes | **all invariants hold** | 46,932 | 609,739 | 21 | ~20 s |
| `MC_all.cfg` | 2 sigils, 3 transitions, **every** header assignment (15³ = 3375 maps), gens 0..2, eager Byzantine votes, symmetry on witnesses, sigils and tids | **all invariants hold** | 687,546 | 5,984,259 | 25 | ~85 s |
| `MC_lazy.cfg` | 2 sigils, 2 transitions, every header assignment, gens 0..1, **explicit `ByzVote`** | **all invariants hold** | 516,656 | 6,091,024 | 22 | ~30 s |
| `MC_mutant.cfg` | `MC.cfg` with `AnyProof = TRUE` (Release accepts any proof) | **Safety violated** (expected) | ~70–90k when found | ~0.5M | 9 | ~5 s |

A 3-sigil version of `MC_all` (gens 0..1, 26³ header maps) did not finish within 10 minutes, so it is not included.

### Mutation counterexample (`MC_mutant.cfg`)

TLC finds the following 7-step trace. z1 is Byzantine and has signed everything.

1. h1 and h2 vote `t2 = {(a,0)}`. With z1, `t2` is **complete**.
2. h3 jumps `a` to generation 1 and votes `t4 = {(a,1),(c,2)}`.
3. h1 and h2 jump `c` to generation 2 and vote `t4`. With z1, `(c,2)` is sealed for `t4`.
4. h1 **releases `a` without a valid proof** (the mutation): `t2` has no death proof, because it is sealed. h1 then votes `t4` at `(a,1)`.
5. `t4` is now complete as well, so sigil `a` is consumed by both `t2` and `t4`.

Under the real Release rule, step 4 is impossible: no death proof for `t2` can exist, because `(a,0)` has only z1 voting against `t2`. This is the honest-intersection argument of §8, case g₁ < g₂.

## Files

* `Sigil.tla`: the protocol, the invariants and the mutation flag.
* `MC.tla`: instance definitions (fixed headers, all headers, symmetry sets).
* `MC.cfg`, `MC_all.cfg`, `MC_lazy.cfg`, `MC_mutant.cfg`: TLC configurations.
* `check.sh`: downloads TLC, runs the configs, and checks that the mutant fails and the others pass.
