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
