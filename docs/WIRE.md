# Sigil Wire Protocol — v0 (draft)

Transport for the witness protocol of [SPEC.md](SPEC.md) §5. v0 uses JSON over HTTP/1.1 because it is easy to inspect and has no dependencies. A binary encoding over HTTP/2 or QUIC is planned for the Rust witness (Phase 2), carrying the same messages.

Nothing a witness sends is trusted. Clients verify votes, seals, charters and proofs exactly as they do in-process.

## Calls

| Method | Path | Body | `ok` result |
|---|---|---|---|
| GET | `/v0/info` | — | `{pk, constellation, version, frozen, stamps: {n, e} \| null}` |
| GET | `/v0/charters` | — | `{cid: [charter, …]}`: every charter chain the witness knows |
| POST | `/v0/spend` | `{request}` (SPEC §5.1) | vote |
| POST | `/v0/release` | `{sigil, proof}` (SPEC §5.2) | new generation (int) |
| POST | `/v0/status` | `{sigil}` (SPEC §5.3) | `{gen, tid, votes}` |
| POST | `/v0/sell_stamp` | `{blinded: hex}` | blind signature (hex) |

Every reply is one JSON object:

* success (HTTP 200): `{"ok": result}`;
* failure: `{"error": kind, "message": str, "vote": vote | null}`. `kind` is one of the following:
  * `conflict` (HTTP 409). The sigil is already bound to another transition at that generation, and `vote` holds the existing vote.
  * `rejected` (HTTP 403). The request was well formed but refused, for example because the lock was not satisfied or the stamp was missing.
  * `bad_request` (HTTP 400). The request was malformed.
  * `internal` (HTTP 500).

Big integers (RSA stamp values) are lowercase hex strings. Request bodies are capped at 1 MiB. A witness handles its calls one at a time and persists state before it answers (SPEC §5).

## Client behaviour

* A witness that cannot be reached counts as crashed. It does not vote, and it can never be assumed to hold no vote (see the wallet's `unpledge_if_unbound`).
* Constellation sizes come from the verified charter, never from how many witnesses answered.
* Charter chains fetched from witnesses are verified against the constellation id (SPEC §3.7) before use. Invalid or forked chains are ignored.

## Gossip

Charter rotations (SPEC §3.7) and equivocation proofs (SPEC §3.8) are public facts that every participant needs. Each one verifies on its own, so they spread by anti-entropy gossip and need no ordering. Witnesses store and serve what they are given. Clients (wallets, or daemons acting for witnesses) run the rounds.

| Method | Path | Body | `ok` result |
|---|---|---|---|
| GET | `/v0/proofs` | — | `{proofs: [proof, …], forks: [fork, …]}`: everything the witness holds |
| POST | `/v0/gossip` | `{charters?: {cid: [charter, …]}, proofs?: [proof], forks?: [fork]}` | `{charters, proofs, forks}`: how many items were new and verified |

* `proof` is `{a: vote, b: vote}` (SPEC §3.8). Only the signed vote fields and `sig` are kept.
* `fork` is `{constellation, prefix: [charter, …], a: charter, b: charter}`. Here `a` and `b` are different charters for version `len(prefix)`, and each is signed by a quorum of `prefix[-1]`. Quorum intersection means at least one member of that version signed both, so a fork shows that the old quorum signed two successors.

**Admission.** Every item is verified before it is stored. Items that fail are dropped silently, and the counts in the reply show what was accepted.
* A chain is accepted only if `Registry.add_chain` accepts it, which means it verifies from the cid and extends the known chain. A chain whose bodies match the known chain but whose signature subsets differ is treated as the same chain, not as a fork. A chain that diverges is never adopted. If both branches verify, the divergence is stored as fork evidence, one item per constellation.
* A proof is accepted only if `verify_equivocation` holds and the accused key belongs to a charter version the receiver knows (`a.constellation`, `a.version`). The receiver keeps one proof per witness key.
* A fork is accepted only if both branches verify against the shared prefix. The receiver keeps one fork per constellation.

On a witness, gossip uses the witness's own charter registry, so a verified rotation is served from `/v0/charters` straight away. Gossip state is not persisted, because it can be learned again from peers.

**Round** (`gossip_round(network, store)` in `sigil/gossip.py`):
1. Pull `/v0/proofs` and `/v0/charters` from every reachable witness.
2. Admit what was pulled, in this order: charters, then forks, then proofs. That way a proof against a member of a rotation learned in the same round is not dropped.
3. Push to each witness the longer chains, proofs and forks it lacks, in batches within the caps.

A wallet builds its store as `GossipStore(network.registry)`, so newly learned charters reach its `TrustPolicy`. It then calls `store.apply(wallet.policy)` to convict every proven equivocator, and from then on that witness's votes no longer count toward seals. `equivocations_in(votes)` extracts proofs from any votes the wallet sees, such as STATUS replies or death proofs.

**Caps.** A message holds at most 64 charter chains, 1024 versions per chain, 64 proofs and 16 forks, within the 1 MiB body limit. A message over any cap is refused as a whole with `bad_request`. A store accepts at most 10 000 new constellations, while extensions of known constellations are always accepted. A client reads at most 16 MiB from one witness per pull.

**Threats.**
* *Spam.* Genesis charters need no signatures, so anyone can mint constellations. The constellation cap bounds this. Proofs against keys outside every known charter are refused, so throwaway keys cannot grow the store. Verification costs at most the signatures that fit in one 1 MiB body.
* *Forgery.* Every item is checked against signatures that chain back to the cid or the vote key. A forged chain, proof or fork is dropped and never forwarded, because only stored items are served.
* *Withholding.* A witness can refuse to serve or forward what it knows. A fact reaches a participant as long as one honest path exists to that participant. Clients pull from every witness, and any single honest relay is enough.
* *Forks.* The first branch seen is kept, so different participants may hold different branches of a forked constellation. Fork evidence then spreads to all of them. A fork proves that the quorum of the forked-from version is compromised, and `fork_signers(fork)` names the keys that signed both branches. Holders should stop trusting that constellation. This is a policy decision, and gossip does not make it automatically. Signing two charters is not a §3.8 vote equivocation, so it does not unlock an `equivocation(witness)` bond.
* *Staleness.* Until a participant learns a rotation, it counts votes against the older charter. Seals made under older versions stay valid (SPEC §9 covers long-range forgery and deep confirmation), so delayed gossip affects liveness, not safety.

## Files

**Network directory**: how a wallet finds witnesses.
```json
{"constellations": {"<cid>": ["http://host:port", "..."]}}
```

**Charter registry**: the verified charter chains a participant starts from.
```json
{"<cid>": [{"body": {...}, "sigs": {...}}, "..."]}
```

## Reference implementation

`sigil/server.py` provides:
* `WitnessServer`, which serves one `Witness` over HTTP;
* `RemoteWitness`, a client with the same interface as `Witness`;
* `RemoteNetwork`, which has the same interface as the in-process `Network`, so `Wallet` runs unchanged against a real network.

`tests/test_wire.py` runs payments, swaps, stamps, conflicts, deep confirmation and crash tolerance over real HTTP.
