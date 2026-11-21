# Sigil Wire Protocol — v0 (draft)

Transport for the witness protocol of [SPEC.md](SPEC.md) §5. v0 uses JSON over HTTP/1.1 because it is easy to inspect and has no dependencies. A binary encoding over HTTP/2 or QUIC is planned for the Rust witness (Phase 2), carrying the same messages.

Nothing a witness sends is trusted. Clients verify votes, seals, charters and proofs exactly as they do in-process. Before that, the reference client (`RemoteWitness`, `RemoteStandby`) treats each of the following as no answer (`Unreachable`):

* a reply larger than its cap: 256 KiB for an ordinary call (a STATUS holds at most one vote per generation), 16 MiB for a charter chain or a gossip pull, and 256 MiB for the operator calls, whose snapshots hold every binding a member has;
* an exchange (connect, request, status line, headers and body) not finished within 4 socket timeouts, or 60 for the operator calls. A watchdog shuts the socket down at the deadline, so a trickled status line or header, or endless `100 Continue` lines, cannot hold a client;
* a redirect, which is never followed;
* a body that is not JSON or not `{"ok": …}`. Memory is bounded by the caps alone: no reply is refused for its content's density, since snapshots, mirror logs, proofs and charters carry what clients sent. Parsed JSON can take about twenty times its size, so at most about 5 MiB for an ordinary reply;
* an `ok` result not of the shape the table below gives for that call, for example a vote with a missing or non-integer `gen`, an INFO whose stamp key is not hex, or a FREEZE snapshot that is not an object of lists;
* a malformed error reply, such as a `conflict` whose `vote` is neither a vote nor null. Any error reply to a GET also counts as no answer.

STATUS votes that are not vote objects are dropped, beyond the first 256 too, and a gossip pull keeps only well-shaped collections. So one Byzantine witness within *f* looks, at worst, like one that is down. A standby member asks every member for a heartbeat at once, so a member that stalls its reply never delays hearing the others. The Rust standby member's probe reads at most 64 KiB, within the same 4-timeout deadline.

A wallet trusts by default only its home and the constellations its directory names (`RemoteNetwork.configured()`), and a client learns only the chain of a constellation it asks about (`GET /v0/charters/<cid>`). It never trusts a chain merely because a witness served it: gossip admits any valid genesis chain from anyone, so an outsider could otherwise plant a constellation whose every key it holds.

## Calls

| Method | Path | Body | `ok` result |
|---|---|---|---|
| GET | `/v0/info` | — | `{pk, constellation, version, frozen, stamps: {n, e} \| null, features}`; `features` lists protocol features the daemon understands (`"checkpoint"`, SPEC §5.7); a daemon from before compaction has no such key |
| GET | `/v0/charters` | — | `{cid: [charter, …]}`: every charter chain the witness knows |
| GET | `/v0/charters/<cid>` | — | `[charter, …]`: the chain of constellation `cid`, `[]` if unknown. Clients ask for the chains they are configured with this way, since gossip admits any valid genesis chain, so `/v0/charters` can grow past what a client reads |
| POST | `/v0/spend` | `{request}` (SPEC §5.1; `request.mirror` carries the mirror acks a version with a successor committee needs, §5.5) | vote |
| POST | `/v0/release` | `{sigil, proof}` (SPEC §5.2) | new generation (int) |
| POST | `/v0/status` | `{sigil}` (SPEC §5.3) | `{gen, tid, votes}`; `rejected` ("witness not active") from a witness that has not joined a charter version (awaiting ADOPT), whose "unbound" would otherwise read as a member's answer |
| POST | `/v0/sell_stamp` | `{blinded: hex}` | blind signature (hex) |
| POST | `/v0/heartbeat` | `{challenge}`: a string of 1 to 128 characters (SPEC §5.5) | `{constellation, version, witness, challenge, sig}`; only an active, unfrozen witness answers |
| POST | `/v0/settle` | `{settlement}`: a settlement certificate `{header, inputs: [{parcel: {home, lock, salt}, seal}]}` (SPEC §3.12, §5.7), at most 512 KiB encoded, every seal from its home's current version | `{settled: [sigil, …]}`: the inputs living here that the witness held bound to exactly the certificate's binding, now settled (rate limited like every public call) |
| POST | `/v0/freeze` (admin) | `{charter, checkpoint?}`: the next charter's body (SPEC §5.4) and, if it carries `checkpoint`, its checkpoint set `[[sigil, gen, tid], …]` (§5.7) | `{sig, snapshot}`; the snapshot leaves out the sigils of the checkpoint set |
| POST | `/v0/adopt` (admin) | `{constellation, version, snapshots: [snapshot, …], checkpoint?}` (SPEC §5.4; `checkpoint` is required when the charter carries one) | `{constellation, version}` |
| POST | `/v0/settled` (admin) | `{}` | `{settled: [[sigil, gen, tid], …], checkpointed: [[sigil, gen, tid], …]}`, sorted by sigil (SPEC §5.7) |

Every reply is one JSON object:

* success (HTTP 200): `{"ok": result}`;
* failure: `{"error": kind, "message": str, "vote": vote | null}`. `kind` is one of the following:
  * `conflict` (HTTP 409). The sigil is already bound to another transition at that generation, and `vote` holds the existing vote.
  * `rejected` (HTTP 403). The request was well formed but refused, for example because the lock was not satisfied or the stamp was missing. A client over its rate limit gets `rejected` with HTTP 429, the message `rate limited` and a `Retry-After` header (seconds), before the call runs (see "Admission control").
  * `bad_request` (HTTP 400). The request was malformed.
  * `internal` (HTTP 500).

Big integers (RSA stamp values) are lowercase hex strings. Request bodies are capped at 1 MiB (the admin calls: 256 MiB, read only after the token is checked). Within that, a SPEND's authorisation `{home, lock, salt, unlock, header}` is at most 32 KiB encoded, a sigil is newly bound only below generation 16, and a RELEASE's death proof is at most 128 KiB (SPEC §5.1, §5.2): anything larger is `rejected` and changes nothing, so no request can make a witness store more than about its own size. A witness handles its calls one at a time and persists state before it answers (SPEC §5). An unlock carries at most 64 equivocation proofs (SPEC §3.5), so one lock evaluation verifies at most 64 of them, far fewer than the ~1,400 a 1 MiB body could hold.

**Portable JSON.** Both daemons refuse (`bad_request`) a request body that is not *portable*: every integer in [−2¹²⁷, 2¹²⁷), no `NaN`/`Infinity` and no float out of range, no string or key holding a lone UTF-16 surrogate, and no value nested more than 256 levels under the body (the admin calls: 272). The Rust parser cannot represent anything else, so the reference refuses it too: a witness of either kind never binds, releases or stores what one of the other kind could not read back from a handover. A FREEZE or SUCCEED snapshot from a Byzantine predecessor may still hold such values; the reference client (`RemoteWitness.freeze`, `RemoteStandby.succeed`) drops every entry that would not be portable inside an `/v0/adopt` or `/v0/standby` body (`portable_snapshot`) before relaying it. Such an entry can never verify, and relaying it would make every adopter refuse the whole handover.

## Rotation

FREEZE is irreversible, so `/v0/freeze` and `/v0/adopt` are operator calls. They need `Authorization: Bearer <token>`, where the witness reads the token from `--admin-token FILE`. A witness started without one refuses them (`rejected`), and so does a request with a wrong token.

* `freeze` answers the witness's signature on the charter body and its evidence `{sigil: log ‖ [{kind: "vote", vote}, …]}`. The witness freezes for exactly one successor: asked again for the same body it answers the same, and for any other it answers `rejected`. A frozen witness never votes or releases again, also after a restart.
* `adopt` runs once, on a witness that has joined no charter version. A retry for the version it adopted answers the same; anything else is `rejected`. The witness must already know the charter `version` (send it by `/v0/gossip` first), and must be a member, else `bad_request`. Malformed parts of a snapshot are skipped, like any other unverifiable evidence, and a sigil left with no verifiable entry gets no record.
* **Checkpoints** (SPEC §5.7). A charter body may carry `checkpoint`: `H("checkpoint", S)` of a checkpoint set `S` (a list of `[sigil, gen, tid]`, sorted by sigil, distinct sigils). `freeze` then needs `S` in the request and answers `rejected` unless every entry matches a record the witness holds settled and every record it holds checkpointed is in `S`; `adopt` needs `S` and answers `rejected` without the exact set. A body without `checkpoint` is hashed as before; `checkpoint` is sent only when the charter has one, so a rotation without settlements reaches older witnesses unchanged. Every member of the next version (and of its committee) must be upgraded before a rotation that carries a checkpoint: an older daemon would adopt such a charter and ignore the set (SPEC §5.7). `RemoteNetwork` checks the `features` each new member announces in `/v0/info`, but that is the daemon's own claim. Never downgrade a witness or standby daemon to a build without checkpoints once its store holds a settled or checkpointed record (store format 2): current Python builds refuse such a store, but a Rust build from just before compaction opens it silently and would treat a checkpointed record as an ordinary binding with no evidence.
* A fresh store joins version 0 directly. A witness for a later version is started with `--adopt` (both daemons): it votes on nothing until ADOPT. A fresh store without `--adopt` refuses to start on a constellation that has rotated.

`RemoteNetwork.rotate(cid, new_urls, admin_token, compact=True)` drives a rotation like `Network.rotate`: it first asks every member for `/v0/settled` and offers the current checkpoint set plus every entry all answering members hold settled (never entries only some hold: those members would refuse to freeze) (a member that does not answer, or an older witness without the call, counts as holding nothing settled); every reachable member freezes for the next charter and signs it; signatures that do not verify are dropped with their evidence; with a quorum, the new chain is gossiped to old and new members, and every new member adopts the union of the signers' evidence. A re-used key whose old process did not sign is left waiting (`RotationIncomplete`), because it must bring its own votes. Every witness and standby member keeps the charter chains it learns (by gossip, ADOPT or STANDBY) in its store (`charter` entries) and merges them into its registry file's chains at start, so a member restarted before its registry file holds the new chain still knows its own version; operators should still add the new chain to their registry files (fresh processes, and proofs and fork evidence learned by gossip, are not persisted).

## Succession

A standby member of a successor committee (SPEC §5.5) is served like a witness (same replies, caps and admission control), by `python -m sigil.witnessd standby` or `sigil-witness standby`:

| Method | Path | Body | `ok` result |
|---|---|---|---|
| GET | `/v0/info` | — | `{pk, role: "standby", constellation, version, fenced, dead, frozen: false, stamps: null}` |
| GET | `/v0/charters`, `/v0/charters/<cid>`, `/v0/proofs`; POST `/v0/gossip` | as for a witness | as for a witness |
| POST | `/v0/mirror` | `{request}`: a SPEND request plus the `version` it is for | mirror ack `{constellation, version, member, sigil, gen, tid, sig}` |
| POST | `/v0/note_release` | `{sigil, entry}`: a release entry `{kind: "release", gen, tid, header, proof}` for a binding it holds | `true` if new, `false` if held already |
| POST | `/v0/status` | `{sigil}` | `{bindings: [[gen, tid], …]}`: every binding of the sigil in its mirror log (holders ask before releasing a pledge, SPEC §4 rule 3) |
| POST | `/v0/standby` (admin) | `{constellation, version, snapshots: [snapshot, …], checkpoint?}`: the handover of a later version, with its checkpoint set if its charter carries one | `{constellation, version}` |
| POST | `/v0/succeed` (admin) | `{charter, sigs?, checkpoint?}`: the next charter's body, the members' signatures on it for a cooperative rotation, and its checkpoint set (it must keep every entry of the version's own set, and equal it for a dead-man takeover, SPEC §5.7) | `{sig, snapshot}`: its signature and its mirror log minus the checkpointed sigils |
| POST | `/v0/settled` (admin) | `{}` | `{settled: [], checkpointed: S}`: the version's checkpoint set |
| POST | `/v0/probe` (admin) | `{urls?}`: member URLs to challenge now (default: `--members`) | `{answered}`: how many valid heartbeats came back |

* Clients collect acks before they ask witnesses to vote: one ack per standby member for the `(constellation, version, sigil, gen, tid)` of the request, and the acks serve every witness of the version. A witness of a version with a committee refuses to create a vote without acks from a quorum of the committee (`rejected`, nothing stored); it checks at most one ack per member. MIRROR refuses an authorisation over 32 KiB, a new binding at generation 16 or above and a fifth transition of one `(sigil, gen)` (SPEC §5.5).
* `--members URL …` and `--probe-every S` make the standby member challenge the members of its version for heartbeats in the background (`--probe-every` 60 in a deployment). The Rust standby heartbeat client requires each member URL to be a root `http://host:port` origin (or bracketed IPv6) on a protected private network; startup rejects unsupported or malformed URLs. An operator-supplied `/v0/probe` URL is checked the same way. It signs a successor only cooperatively (`sigs` holds a quorum of the version's members' signatures on it) or once fewer than a quorum of members answered during the last `dead_man` seconds and it has stood by that long; a restart starts a new observation window.
* `RemoteNetwork.probe` forwards the directory's member URLs to each standby's `/v0/probe`. It returns a count only when every configured standby answers; a refusal or unreachable standby raises instead of being reported as zero live members. With a Rust standby and a public HTTPS client directory, call its `/v0/probe` without `urls` to use its configured private HTTP `--members` list.
* A standby member signs one successor per version and fences for it (also after a restart): asked again for the same body it answers the same, for any other `rejected`; once fenced it acknowledges and stores nothing for that version. A fresh store stands by for version 0 at once; for a later version start it with `--wait` and send the handover with `/v0/standby`. `standby`, `succeed` and `probe` are operator calls (`--admin-token FILE`), never rate limited.

`RemoteNetwork(directory, committees={cid: [standby URL, …]})` sends acks with every payment. `RemoteNetwork.succeed(cid, new_urls, admin_token, committee_urls=…, dead_man=…)` drives a dead-man takeover in two phases: it first reads `dead` from each standby member's `/v0/info` and sends SUCCEED only if a quorum reports the version dead (a member that signs fences at once, so a minority must never be asked alone; a successor body some member signed must be completed, never abandoned); then each standby member signs the next charter only if the dead-man condition holds for it; with a quorum, the new chain is gossiped, the new members adopt the signers' mirror logs, and the new committee (if any) enters standby with the same handover. `RemoteNetwork.rotate` of a version with a committee also asks the committee to co-sign, passing the members' signatures as the request. A charter's `successor` clause is set at genesis with `witnessd genesis --committee K … --dead-man S` (both daemons).

## Admission control

A witness on the open network must not serve every request of every client (SPEC §5.6). Both daemons apply these rules, with the same defaults:

* **Rate limit.** Each client has a token bucket of `--rate-burst` tokens (default 100) that refills at `--rate-limit` tokens per second (default 20). Every call costs one token, except the rotation calls, which are refused before their body is read unless they carry the admin token. A call with no token left is answered HTTP 429 (`rejected`, `rate limited`, `Retry-After`) and never reaches the witness, so it changes no state. A client is an IPv4 address, or an IPv6 /64 (one subscriber usually holds a whole /64). At most 65,536 buckets are kept; the least recently seen is forgotten first, which only ever gives that client a full bucket again.
* **Default.** The limit is on when the daemon listens on a non-loopback address (`--host 0.0.0.0`, a public address, a hostname other than `localhost`) and off on loopback, so tests and the local testnet (`testnet/`) run unlimited. `--rate-limit 0` turns it off anywhere; `--rate-limit R` turns it on anywhere. The Docker testnet (`docker-compose.yml`) listens on 0.0.0.0 inside its containers but publishes on 127.0.0.1 only, so it passes `--rate-limit 0`.
* **Connections.** At most 256 connections are open at once, and, with a rate limit, at most 16 from one client; a connection over a cap is closed unread. A connection whose client sends nothing (no request, or a stalled body) or accepts nothing for 30 seconds is closed (the Rust witness gives a request body 30 seconds in all, and an authorised ADOPT body unlimited time).

Why a rate limit and not stamps by default: stamps (SPEC §3.10) price attention, but `/v0/sell_stamp` blind-signs for anyone who asks, since the protocol leaves payment to the deployment. Stamps on by default would therefore limit nothing, and each sale costs the witness an RSA-2048 signature. A per-client bucket needs no payment system and bounds what one address can make a witness do. It does not stop an attacker with many addresses; a deployment that can take payment should also require stamps (`--stamps`, with `sell_stamp` behind the payment) and put the witness behind a network-level filter. A reverse proxy in front of a witness makes every client the proxy's address; give the proxy its own limits and run the witness with `--rate-limit 0`.

**Stamp key recovery.** Back up `<store>.stamps.json` with the witness store: losing it invalidates stamps already sold. Both daemons pin its public key in store format 3 when `--stamps` first starts, then refuse startup if the sidecar is missing or changed. Older daemons refuse format 3, so they cannot silently rotate the key after a rollback. An existing store without a sidecar requires `--init-stamps` to enable stamps for the first time. Stores from before key pinning adopt an existing sidecar on their next stamped start; if that sidecar was lost, restore the original before starting. Use `--init-stamps` only when that store has never sold stamps; a store with redeemed stamps refuses this flag.

## Client behaviour

* A witness that cannot be reached counts as crashed. It does not vote, and it can never be assumed to hold no vote (see the wallet's `unpledge_if_unbound`).
* A request may be delayed in flight and reach a witness after the client gave up on it. Witnesses refuse to newly bind on an authorisation whose `unlock.expires` has passed (SPEC §5.1), so a wallet releases a failed pledge only after `expires` plus a clock-skew margin, and only if every current member answered STATUS with no binding or vote for it (SPEC §4 rule 3).
* Constellation sizes come from the verified charter, never from how many witnesses answered.
* Charter chains fetched from witnesses are verified against the constellation id (SPEC §3.7) before use. Invalid or forked chains are ignored.
* A `rejected` reply with HTTP 429 means "not now": the reference client raises `Rejected("rate limited")`, like any refusal, and the witness counts as not having voted.

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
* A fork is accepted only if both branches verify against the shared prefix. The receiver keeps one fork per constellation, and at most 10 000 forks in all (anyone can fork a constellation whose keys they minted).

On a witness, gossip uses the witness's own charter registry, so a verified rotation is served from `/v0/charters` straight away. Gossip state is not persisted, because it can be learned again from peers.

**Round** (`gossip_round(network, store)` in `sigil/gossip.py`):
1. Pull `/v0/proofs` and `/v0/charters` from every reachable witness.
2. Admit what was pulled, in this order: charters, then forks, then proofs. That way a proof against a member of a rotation learned in the same round is not dropped.
3. Push to each witness the longer chains, proofs and forks it lacks, in batches within the caps.

A wallet builds its store as `GossipStore(network.registry)`, so newly learned charters reach its `TrustPolicy`. It then calls `store.apply(wallet.policy)` to convict every proven equivocator, and from then on that witness's votes no longer count toward seals. `equivocations_in(votes)` extracts proofs from any votes the wallet sees, such as STATUS replies or death proofs.

**Caps.** A message holds at most 64 charter chains, 1024 versions per chain, 64 proofs and 16 forks, within the 1 MiB body limit. A message over any cap is refused as a whole with `bad_request`. A charter names at most 128 witnesses and encodes to at most 64 KiB (SPEC §3.7); a chain holding a larger one does not verify, so it is dropped like any invalid item. A store accepts at most 10 000 new constellations, while extensions of known constellations are always accepted. A client reads at most 16 MiB from one witness per pull. If a witness holds more chains than that, the client asks for the chains of the constellations it is configured with one by one (`GET /v0/charters/<cid>`).

**Threats.**
* *Spam.* Genesis charters need no signatures, so anyone can mint constellations. The constellation cap bounds how many, the charter caps how large each version is (before them, one message registered a 14,000-witness charter), and the rate limit how fast. Proofs against keys outside every known charter are refused, so throwaway keys cannot grow the store. Verification costs at most the signatures that fit in one 1 MiB body.
* *Forgery.* Every item is checked against signatures that chain back to the cid or the vote key. A forged chain, proof or fork is dropped and never forwarded, because only stored items are served.
* *Withholding.* A witness can refuse to serve or forward what it knows. A fact reaches a participant as long as one honest path exists to that participant. Clients pull from every witness, and any single honest relay is enough.
* *Forks.* The first branch seen is kept, so different participants may hold different branches of a forked constellation. Fork evidence then spreads to all of them. A fork proves that the quorum of the forked-from version is compromised, and `fork_signers(fork)` names the keys that signed both branches. Holders should stop trusting that constellation. This is a policy decision, and gossip does not make it automatically. Signing two charters is not a §3.8 vote equivocation, so it does not unlock an `equivocation(witness)` bond.
* *Staleness.* Until a participant learns a rotation, it counts votes against the older charter. Seals made under older versions stay valid (SPEC §9 covers long-range forgery and deep confirmation), so delayed gossip affects liveness, not safety.

## Files

**Network directory**: how a wallet finds witnesses, and the standby members of a home that has a successor committee (SPEC §5.5), from which a wallet collects mirror acks before witnesses will vote.
```json
{"constellations": {"<cid>": ["http://host:port", "..."]},
 "committees":     {"<cid>": ["http://host:port", "..."]}}
```
`committees` is optional.

**Charter registry**: the verified charter chains a participant starts from.
```json
{"<cid>": [{"body": {...}, "sigs": {...}}, "..."]}
```

## Reference implementation

`sigil/server.py` provides:
* `WitnessServer`, which serves one `Witness` over HTTP, and `StandbyServer`, which serves one standby member (`sigil.succession.Standby`);
* `RemoteWitness` and `RemoteStandby`, clients with the same interfaces as `Witness` and `Standby`;
* `RemoteNetwork`, which has the same interface as the in-process `Network`, so `Wallet` runs unchanged against a real network.

`tests/test_wire.py` runs payments, swaps, stamps, conflicts, deep confirmation and crash tolerance over real HTTP, `tests/test_rotation_wire.py` runs rotations, and `tests/test_succession_wire.py` successions.

The Rust witness (`rust/sigil-witness`) serves every call above with the same semantics, and `sigil-witness standby` every standby call. `bench/interop.py` checks this with the Python wallet against Rust witness processes and mixed Rust+Python constellations, including rotation, stamps, gossip, and a dead-man takeover of a mixed home by a mixed committee.
