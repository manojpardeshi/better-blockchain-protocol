# Benchmarks: Rust witness vs Python reference

Phase 2 (#9) adds a second witness implementation in Rust (`rust/sigil-witness`). It speaks
the v0 wire protocol of [WIRE.md](WIRE.md) and is byte-compatible with the Python reference.
This page shows what it costs to run a witness and to verify what witnesses produce, and how
those numbers were measured.

**Headline (median of 3 runs; one machine; localhost):**

| | Python reference | Rust | Ratio |
|---|---:|---:|---:|
| Votes/s per core, in-process, CPU only (no store) | 2 792 | 9 911 | 3.5× |
| Votes/s, in-process, 4 threads, CPU only | (GIL: 1 core) | 24 419 | 8.7× |
| Votes/s, in-process, durable, 1 request at a time | 1 013 | 1 114 | 1.1× (fsync-bound) |
| Votes/s, in-process, durable, 32 concurrent requests | (serial) | 6 454 | 6.4× (group commit) |
| Votes/s over HTTP, witness pinned to 1 core, durable, 16 clients | 602 | 2 916 | 4.8× |
| Votes/s over HTTP, 1 core, no store (CPU bound) | — | 6 941 | — |
| Payment latency, Python wallet with 4 witnesses, p50 | 19.2 ms | 14.5 ms | 1.3× |
| Seal verification, n = 31 (q = 21) | 2.58 ms | 0.65 ms (batch) | 4.0× |

Paying with a Python wallet barely gets faster with Rust witnesses, because the wallet is
the bottleneck: it contacts the witnesses one after another, verifies every vote, and the
recipient verifies the whole dossier. A Rust witness is mostly an operator win. It gives
3.5× more votes per core and, with group commit, about 5× more durable votes per disk flush
under concurrent load.

## Machine

| | |
|---|---|
| CPU | Intel Xeon (Cascade Lake, AVX-512), 4 vCPUs, reported at 2.10 GHz (2.80 GHz in an earlier session on the same image) |
| Virtualisation | container inside a Firecracker microVM (kernel 6.18.44-fc), shared host |
| Disk | virtio block device, ext4; raw `fdatasync` p50 0.17 ms, p99 0.5–1.2 ms during the run (it was bimodal at times, with p50 up to 4 ms between runs) |
| Software | Python 3.13.16, `cryptography` 50.0.1 on OpenSSL 3.0.13; rustc 1.97.0, `ed25519-dalek` 2.2 (AVX2 backend), `blake2b_simd` 1, `redb` 2.6, `axum` 0.7 / `tokio` 1 |

The raw data is in [`bench/results.json`](../bench/results.json). It holds every run, the
fsync probes taken before and after, and the machine description.

## How to reproduce

```sh
cargo build --release --manifest-path rust/Cargo.toml
python3 bench/run_all.py            # ~15 min; --quick for a smoke run; writes bench/results.json
python3 bench/interop.py            # wire-compatibility check (not a benchmark)
```

Individual pieces:

```sh
rust/target/release/sigil-bench inproc --n 20000 --threads 1 --store memory|redb
rust/target/release/sigil-bench seal   --sizes 4,7,10,31,100
rust/target/release/sigil-bench http   --url http://127.0.0.1:7000 --n 20000 --concurrency 16 [--new-conn]
rust/target/release/sigil-bench micro  # cost of each primitive
rust/target/release/sigil-bench fsync  --dir /tmp
python3 bench/bench_python.py inproc [--store] | seal | dossier --lengths 1,10,100,1000 | latency --kind rust|python
```

## Methodology

* **What one vote costs.** Each spend request is a fresh one-input transition with a
  `sig(pk)` lock and an owner signature in the `{sigil, tid, expires}` format. Requests are
  **pre-generated**, because owner signing is client work. A timed vote includes, for both
  implementations:
  * parsing the JSON request bytes;
  * the authorisation check (sigil hash, header checks, transition id, one Ed25519 verify);
  * the record update;
  * signing the vote (one Ed25519 signature);
  * persisting the record, when a store is used;
  * encoding the reply.
* **In-process.**
  * Python: `sigil.witness.Witness`, run with no store or with `sigil.store.WitnessStore`
    (SQLite, WAL, `synchronous=FULL`).
  * Rust: `Witness` with the in-memory store or with the redb store (`Durability::Immediate`).
  * Each run uses a new store file.
  * "1 thread, durable" waits for each vote to be durable before submitting the next request.
    That is the latency-bound case, and it measures fsync more than code.
* **HTTP.**
  * The witness process is pinned to CPU 0 (`taskset -c 0`); the Rust witness also runs with
    `--threads 1`.
  * The load generator (`sigil-bench http`, Rust, blocking sockets) is pinned to CPUs 1–3, so
    the result is per witness core.
  * It uses keep-alive connections. `--new-conn` opens a TCP connection per request, as
    Python's `urllib` does. The Python server is HTTP/1.0, so it closes the connection every
    time either way.
  * Latencies are per request, measured at the client.
* **Payment latency.**
  * A Python `Wallet` (alice) pays another (bob) one unit, 200 times, through
    `RemoteNetwork`. The constellation is 4 witness processes on localhost (unpinned), all
    Rust or all Python.
  * The time covers everything `Wallet.pay` does:
    * selecting coins, building the transition, authorising it;
    * one `spend` round trip to each of the 4 witnesses, sequentially, with vote and seal
      verification;
    * bob's full receive: dossier verification, plus `status` at all 4 witnesses.
  * "Seal only" times just the witness round trips.
* **Repetition.** Every configuration ran 3 times, with Rust and Python interleaved. The
  tables give the median; the range is in `results.json`.
* **Holder-side verification (Python only).**
  * One coin is passed back and forth L times between two wallets. Each hop has 1 input and
    1 output, so the parcel's ancestry has L + 1 transitions and L seals.
  * A fresh `Verifier` (nothing cached) verifies the received parcel from its dossier.
  * "Warm one hop" is a verifier that already accepted the history checking one more hop.

## Results

### Votes per second, in-process

| Configuration | Python | Rust |
|---|---:|---:|
| No store, 1 thread | 2 792 (358 µs/vote) | 9 911 (98–160 µs/vote) |
| No store, 4 threads | — (GIL) | 24 419 |
| Durable, 1 thread, one request at a time | 1 013 | 1 114 |
| Durable, 32 threads (group commit) | — | 6 454 |

Where a Rust vote's time goes (`sigil-bench micro`, callgrind on `inproc`):

* About 80% is Ed25519: one verify (≈ 40–53 µs) and one sign (≈ 25 µs).
* Key decompression is ≈ 5 µs.
* JSON parsing, canonical encoding and BLAKE2b together are under 10 µs.

Python spends about 160 µs per verify and 55 µs per sign, including key loading and
canonical encoding.

**Durable, one at a time.** Both implementations are bound by the disk flush here: SQLite
in WAL mode needs one fsync per commit, and redb needs one (its 1PC + checksum commit). They
come out level.

**Group commit.**

* The Rust witness verifies requests concurrently.
* It submits each record update to a single writer thread while holding the state lock.
* The writer commits everything that has queued up in **one redb transaction with one
  fsync**.
* Every reply waits until all writes submitted before it read state are durable, so the
  persist-before-answering rule of SPEC §5 holds.
* With 32 concurrent requests this gives about 6× the durable throughput of one-at-a-time.

**Scaling with threads (no store):** 1 thread 8 458, 2 threads 15 440, 4 threads 22 131 votes/s
in a separate run. An earlier version signed the vote while holding the state lock and only
reached 1.2× with 4 threads. The vote's contents are fixed before the lock is taken (sigil,
generation, tid, time), so it is now signed outside the lock. Scaling is still sub-linear: the
remaining serial work is cloning the record under the lock, plus allocator and lock traffic.

### Votes per second over HTTP (witness pinned to one core)

| Witness | Store | Clients | Votes/s | p50 | p99 |
|---|---|---:|---:|---:|---:|
| Python `sigil.witnessd` | SQLite | 1 | 537 | 1.6 ms | 3.6 ms |
| Python `sigil.witnessd` | SQLite | 16 | 602 | 24.6 ms | 50.9 ms |
| Rust `sigil-witness` | redb | 1 | 951 | 1.0 ms | 3.7 ms |
| Rust `sigil-witness` | redb | 16 | 2 916 | 5.4 ms | 9.8 ms |
| Rust `sigil-witness` | redb | 16, new TCP connection per request | 2 401 | 6.4 ms | 12.5 ms |
| Rust `sigil-witness` | redb | 64 | 3 149 | 19.0 ms | 40.6 ms |
| Rust `sigil-witness` | memory (benchmark only) | 16 | 6 941 | 2.3 ms | 4.5 ms |

* The Python witness serialises its calls under one lock and the GIL, so more clients only
  queue.
* On one core, the Rust witness's durable throughput is limited by CPU (HTTP and crypto)
  more than by fsync. Without a store it reaches 6 941 votes/s, about 70% of its in-process
  rate; the gap is HTTP and tokio overhead.

### End-to-end payment latency (Python wallet, 4 witnesses, localhost)

| Witnesses | `pay` p50 | `pay` p99 | seal only p50 | seal only p99 |
|---|---:|---:|---:|---:|
| 4 × Python | 19.2 ms | 26.3 ms | 12.4 ms | 18.3 ms |
| 4 × Rust | 14.5 ms | 20.4 ms | 9.6 ms | 13.6 ms |

* Most of a payment is wallet-side Python:
  * about 7 sequential HTTP requests through `urllib`;
  * 4 + 3 vote verifications at roughly 160 µs each;
  * the recipient's receive, which verifies the new transition and its seal, then queries
    STATUS at every witness.
* A wallet that asked all witnesses in parallel would pay one round trip instead of four,
  about 2–3 ms with Rust witnesses.
* Finality latency is set by the client, not by the witness.

### Seal and death-proof verification

| n (quorum) | Python `verify_seal` | Rust single | Rust batch | Rust death proof single | Rust death proof batch |
|---|---:|---:|---:|---:|---:|
| 4 (3) | 354 µs | 147 µs | 96 µs | 133 µs | 117 µs |
| 7 (5) | 591 µs | 287 µs | 136 µs | 219 µs | 137 µs |
| 10 (7) | 883 µs | 284 µs | 187 µs | 332 µs | 184 µs |
| 31 (21) | 2 578 µs | 942 µs | 652 µs | 1 098 µs | 554 µs |
| 100 (67) | 8 066 µs | 3 056 µs | 1 944 µs | 3 190 µs | 1 748 µs |

* Batch verification (`ed25519_dalek::verify_batch`) saves 30–50% at realistic quorum sizes.
* If a batch fails, every signature is checked again individually. One bad vote therefore
  costs a full single pass on top of the batch.
* The witness uses batching for death proofs (RELEASE) and for equivocation proofs inside
  `equivocation` locks. `--no-batch-verify` turns it off.

### Holder-side dossier verification (Python reference), by history length

| History (hops) | Transitions | Dossier size | Cold verify | Per transition |
|---:|---:|---:|---:|---:|
| 1 | 2 | 3.4 KB | 0.73 ms | 364 µs |
| 10 | 11 | 25 KB | 7.7 ms | 699 µs |
| 100 | 101 | 243 KB | 66 ms | 654 µs |
| 1 000 | 1 001 | 2.4 MB | 718 ms | 718 µs |

* Cost and size grow **linearly** with history: about 0.7 ms and 2.4 KB per hop with
  n = 4. Each hop carries a 3-vote seal plus the owner's unlock.
* Most of the cost is Ed25519 verification: q = 3 vote signatures and 1 owner signature per
  spend.
* A holder that already verified the history pays only for what is new: one extra hop costs
  2.9 ms warm. That includes `ancestry()` on the sender's side and charter checks, not only
  the 4 signatures.
* This linear growth is the "dossier growth" open problem of the whitepaper, and the reason
  recursive proofs are on the roadmap.
* Porting the verifier to Rust would cut the constant by roughly 3–4×, going by the seal
  numbers above. It would not change the slope.

## Caveats

* **One machine, localhost.**
  * Network round trips are about 0.1 ms.
  * The load generator shares the VM with the witness. It runs on other cores, but the
    hypervisor is shared.
  * Real deployments add WAN latency to every round trip: a payment costs about 1 RTT per
    witness with the reference wallet (sequential), or about 1 RTT with a parallel client.
* **The disk is virtual.** `fdatasync` latency on this VM moved between about 0.2 ms and
  about 4 ms from one minute to the next. On local NVMe without a volatile write cache,
  expect durable single-stream rates to be bound by the device's flush latency in the same
  way, for both implementations.
* **CPU frequency** reported by the guest changed between sessions (2.8 → 2.1 GHz). All
  numbers in the tables come from the same run.
* **Python numbers include interpreter overhead** that a C-accelerated JSON or crypto path
  could reduce. The reference was not written for speed.
* The in-memory store exists only for benchmarks (`--unsafe-memory-store`). A witness
  without durable state can equivocate after a restart.

## The Rust witness

`rust/sigil-witness`:

* is a library plus the `sigil-witness` binary;
* uses the same files and flags as `python -m sigil.witnessd`;
* `run` takes `--key`, `--registry`, `--constellation`, `--store`, `--host`, `--port`,
  `--stamps`, `--admin-token FILE` and `--adopt`;
* also provides `keygen` and `genesis`;
* reads key files `{"seed", "pk"}` and charter registries `{cid: [charter…]}` written by the
  Python daemon, and the reverse works too.

**Implemented**

* SPEC §5.1 SPEND, including the owner-signed `expires`:
  * `unlock_message = {sigil, tid, expires}`;
  * `expires` must be an integer;
  * a sigil is never *newly* bound once the clock is past `expires`; re-voting an existing
    binding is allowed.
* §5.2 RELEASE, with home-bound death proofs of both kinds (§3.9).
* §5.3 STATUS.
* The complete lock language (§3.5): sig, multi, after/before (witness clock), hash,
  equivocation, all/any and never, with the same well-formedness rules and node budget.
* Charter chain verification.
* Durable state with group commit.
* §5.4 rotation: FREEZE binds to one successor (its hash is the persisted `frozen` value, the
  same successor is re-signed, any other refused) and hands over the log plus the witness's
  own votes; ADOPT is the reference's fixed rule (a lone live binding is inherited only without
  a sibling at its generation, otherwise CONTESTED with `candidates`; a re-used key abstains
  where it already voted); RELEASE of a CONTESTED record removes the candidates a proof kills.
  A new member is started with `--adopt` and waits for `/v0/adopt`.
* §3.10 stamps: blind RSA-FDH selling (`/v0/sell_stamp`), one redemption per serial on SPEND,
  redeemed serials in the store, the key in `<store>.stamps.json` (the reference's file and
  format, created on first use).
* Gossip storage (WIRE.md "Gossip"): chains extend the witness's registry, fork evidence and
  equivocation proofs are kept with the reference's admission rules and caps.

**Endpoints**: every call of WIRE.md, with the same semantics: `/v0/info`, `/v0/charters`,
`/v0/spend`, `/v0/release`, `/v0/status`, `/v0/sell_stamp`, `/v0/proofs`, `/v0/gossip`, and the
operator calls `/v0/freeze` and `/v0/adopt`. SPEND, RELEASE, gossip, FREEZE and ADOPT run on the
blocking thread pool, never on the async workers.

**Store**: the store kinds of `sigil/store.py` (`pk`, `member`, `frozen`, `record`, `stamp`);
records carry `candidates`, and stores written before rotation was ported load unchanged.

**Byte compatibility** is checked by golden vectors generated from the Python reference
(`rust/sigil-witness/tests/gen_vectors.py` → `vectors.json`, checked in and compared in CI):

* 2 592 canonical-JSON cases, including random IEEE-754 floats, astral characters,
  control characters and big integers, each with its BLAKE2b digest;
* Ed25519 keys and signatures from Python seeds;
* sigils, body hashes and transition ids;
* 36 lock cases evaluated at four clock values, including the 64-proof cap;
* seals, equivocation proofs and death proofs;
* a 33-step scripted run of a reference witness that the Rust witness replays. Every vote
  must match byte for byte, and every rejection must have the same kind and message;
* a 68-step rotation script on three witnesses: FREEZE (wrong predecessor, the same successor
  twice, a second successor), ADOPT by a new key (with junk evidence) and by a re-used key
  (own-vote abstention), full records after ADOPT, RELEASE of CONTESTED records, and both
  rotation regressions of `tests/test_conformance.py`;
* stamps: full-domain hashes, blind signatures, 12 verification cases, and a 16-step script of
  a stamp-selling witness (sale, redemption, double redemption, forged and missing stamps);
* a 22-step gossip script: chains, a fork, proofs, forks and every per-message cap.

`bench/interop.py` then starts Rust witness processes from Python-generated files and drives
them with `sigil.server.RemoteNetwork` and `sigil.wallet.Wallet`. It covers:

* issue and pay across constellations;
* deep confirmation;
* a constellation of 2 Rust and 2 Python witnesses whose seals mix votes from both;
* an atomic swap across two constellations;
* a double-spend conflict;
* RELEASE of a dead swap, then a respend at generation 1;
* authorisation expiry and time locks;
* SIGKILL and restart on the same store, after which the witness returns the same vote byte
  for byte and refuses the conflicting spend;
* the error kinds for malformed requests;
* rotation with `RemoteNetwork.rotate` from 4 Rust witnesses to 2 Rust and 2 Python ones (one a
  re-used key): bindings inherited, frozen witnesses refuse, payments continue and deep
  confirmation works under the new version, restarts keep both sides' state, and the rotation
  calls are refused without the admin token;
* the two rotation regressions of `RotationRegressionTests`, one on Rust witnesses and one on
  mixed Rust+Python constellations in both versions;
* stamps on a constellation of 3 Rust and 1 Python witnesses: sale, single redemption, the key
  and redeemed serials across a SIGKILL, and wallet payments with stamps;
* gossip: an equivocation proof, a rotation and a fork told to single witnesses reach every Rust
  and Python witness and the wallet through `gossip_round`, and junk and oversized messages
  are refused.

### Compatibility notes (deliberate differences)

The rule is that **the Rust witness may refuse what the reference accepts, never the
reverse** (with one exception, batch verification, below). Refusing only makes a witness
abstain, which the protocol tolerates.

* **Seal vote entries must be exactly `{witness, time, sig}`.** The reference builds votes as
  `dict(common, **entry)`, so extra keys in an entry *override* the seal's
  `constellation`/`version`/`sigil`/`gen`/`tid`. As a result, the reference
  (`sigil/proofs.py` `votes_of_seal`) accepts:
  * a "death proof" made from the real seal of the very transition it claims is dead. The
    seal-level `tid` is changed and each entry overrides it back, so any holder of a seal can
    release a sealed input and the owner can then double-spend.
  * a seal claiming any `(home, sigil, gen, tid)` made from votes of an attacker-run
    constellation (entries override `constellation`), which holder validation then accepts.

  Both are demonstrated by vectors (`"python": true, "rust": false`). The Python fix is a
  one-liner in `votes_of_seal`: reject entries whose keys are not exactly
  `{"witness", "time", "sig"}`, or build `dict(v, **common)` so the seal's fields win.
* **Strict typing.** Strings must be strings and integers must be integers, not booleans or
  floats, wherever the reference would compare across types (`1 == True == 1.0` in Python).
  Generations must be below 2^62. Header inputs must be `[str, int]` pairs.
* **JSON the reference accepts but Rust cannot represent:** lone UTF-16 surrogates,
  `NaN`/`Infinity`, integers beyond i128, nesting deeper than 256, and non-UTF-8 bodies.
  These are answered `bad_request`.
* **Batch verification** (death proofs, equivocation proofs):
  * `verify_batch` checks the same cofactorless equation as single verification, with random
    coefficients derived from the inputs.
  * A signature whose `R` or key has a small-order component can pass the batch while
    failing single verification (OpenSSL in Python, dalek single in Rust).
  * Crafting such a signature needs a valid signature on the same message, or the signer's
    own key, so it attests the same fact. Accepting it does not affect safety (Lemma 2 counts
    Byzantine votes as votes), but such an edge-case proof could be accepted by Rust and
    refused by Python.
  * `--no-batch-verify` gives exact parity.
* **Concurrency.**
  * Calls are served concurrently.
  * Signature checks run outside the state lock.
  * A SPEND signs its vote before taking the lock, because the vote's contents are already
    fixed. A vote that is not needed is discarded and never sent.
  * The record update is serialised and made durable (group commit) before any reply that
    depends on it.
* **Store format** is redb, not the reference's SQLite log, so stores are not interchangeable
  between implementations. Keys, registries, stamp keys and the wire are.
* **Hex in stamps** must be plain `[0-9a-fA-F]+`. Python's `int(x, 16)` also takes a sign, a
  `0x` prefix, underscores and surrounding whitespace (vectors `"python": true, "rust": false`).
* **Gossip order within one message**: the reference admits a message's charter chains in the
  order the JSON lists them, Rust in key order. This only matters when the store reaches its
  10 000-constellation cap within one message.
