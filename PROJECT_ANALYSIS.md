# Project Analysis: Sigil

## Executive summary

Sigil is a research prototype for a **chainless value-transfer protocol**. It deliberately avoids blocks, miners, a global ledger, a transaction ordering mechanism, and a native token. Rather than asking a whole network to agree on every transaction, it treats double-spending as a conflict local to one unit of value.

Each unit of value is a **parcel**. A group of witnesses, called a **constellation**, attests that its opaque single-use identifier (a **sigil**) was consumed once. A quorum of witness votes forms a **seal**. The recipient receives a portable proof history, called a **dossier**, and validates ownership, asset conservation, seals, and trusted witness groups locally.

The intended result is deterministic finality once a valid witness quorum seal is obtained, without a blockchain-wide ordering bottleneck. Completion in one round trip depends on witness availability and the protocol's trust assumptions.

## How a payment works

1. The recipient creates a fresh, one-time address and chooses the constellation that will be the parcel's home.
2. The payer's wallet constructs a transition, signs the spend conditions for its input parcels, and asks the home witnesses to vote.
3. Witnesses see only the sigil, transition header, lock, and authorization. They do not receive the asset, amount, or recipient information.
4. A quorum of matching votes becomes a seal.
5. The payer sends the recipient the relevant dossier; the recipient independently validates the complete history before accepting the parcel.

This shifts responsibility that a blockchain normally places on the network into the wallet and recipient-side verifier.

## Architecture

The Python package is the readable reference implementation:

- `sigil/model.py`, `encoding.py`, and `crypto.py` define canonical protocol objects, hashes, and signatures.
- `sigil/wallet.py` creates, authorizes, seals, receives, retries, and recovers payments.
- `sigil/witness.py` implements the per-sigil vote-once state machine.
- `sigil/validate.py` validates dossiers, locks, seals, trust policies, and asset conservation.
- `sigil/store.py` provides durable SQLite-backed witness state.
- `sigil/server.py` and `sigil/witnessd.py` provide the v0 JSON-over-HTTP daemon and remote client.
- `sigil/swap.py` supports multi-party and cross-constellation atomic swaps.
- `sigil/charter.py` and `sigil/succession.py` handle witness membership rotation and successor committees.
- `sigil/stamps.py`, `sigil/ratelimit.py`, and `sigil/gossip.py` cover blind fee stamps, admission control, and evidence propagation.

There is also a Rust workspace with a wire-compatible witness implementation, benchmarks, and proof-related tooling. The repository includes a file-based CLI, a local multi-process testnet, and a Docker Compose setup for a four-witness test constellation.

## Important protocol properties

- No global ordering: independent parcels can be processed in parallel.
- Holder-side validation: the receiver checks that the history is valid and value is conserved.
- Privacy by limited witness visibility: witnesses do not receive the transaction body.
- Deterministic finality: a valid witness quorum seal is final for that input.
- Fault tolerance: a constellation of `n` witnesses targets tolerance for `floor((n-1)/3)` Byzantine faults and requires a quorum of `n - f`.
- Recovery: failed multi-party transfers can be released with a death proof; wallets persist pledges before sending authorizations to avoid crash-induced equivocation.
- Membership continuity: rotation and successor committees preserve relevant evidence when a witness group changes or becomes unavailable.

## Current maturity

This is a substantial research implementation, not a production payment network. It has unusually strong verification material for a prototype:

- TLA+/TLAPS formal models and proofs in `formal/`
- Python model checking, fuzzing, conformance, red-team, chaos, and real-process integration tests
- Rust/Python interoperability and golden-vector tests

Local verification completed successfully on 2026-11-14: `python3 -m unittest discover -v` ran **249 tests** successfully in about 106 seconds. It emitted one non-fatal SQLite resource warning from a test that leaves a store connection open; this is a test cleanup issue, not a demonstrated protocol failure.

## Main risks and open work

- It is explicitly labelled an unaudited v0 research prototype.
- Dossiers grow with transaction history; recursive succinct proofs are still research work.
- Losing a wallet's dossier can mean losing access to the associated value, so backup is fundamental.
- Witness and successor-committee availability affects liveness during outages and partitions.
- Shared-state applications such as AMMs, auctions, and DAOs are not yet solved product areas.
- Stamp pricing, bond sizing, an external public testnet, and an independent audit remain roadmap items.
- The wire protocol is JSON over HTTP and uses bearer-token operator endpoints. Any real deployment would need TLS, strict network isolation, operational hardening, and a security review. The included Compose configuration is intended for local testing, not public deployment.

## Recommended next steps

1. Close the implementation and operations gaps before handling real value. The formal proofs cover abstract protocol models; wallet logic, networking, persistence, Rust code, and liveness have narrower evidence. In particular, swaps between separate processes still have unresolved fair-exchange requirements (`docs/VERIFICATION.md` §5).
2. Prepare a protected testnet run by independent operators. Protect the HTTP transport and operator credentials, isolate each operator's private keys, exercise backup and recovery, and test outages and partitions before inviting outside operators.
3. Define stamp pricing and bond sizing before economic security claims or real-value use. Continue dossier-growth and privacy research in parallel; prioritize shared-state features when a concrete application requires them.

The risk summary in `docs/AI_THREAT_MODEL.md` should also be refreshed: it still describes several bugs as active even though its findings table marks them fixed. Those fixes are real progress, but passing tests and abstract proofs do not establish production readiness.

## Bottom line

Sigil is best understood as an attempt to make digital cash-like transfers work through portable proofs and per-coin witness quorums instead of a universally ordered blockchain. The repository is thoughtfully designed and extensively tested for a research prototype. Its next milestone is a protected, independently operated testnet that can expose implementation and availability failures before an audit and any real-value deployment.
