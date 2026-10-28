# Sigil Roadmap

Priority: **prove it first**. Every phase ends with something testable, and the riskiest unknowns are tackled first. The production witness will be written in **Rust**. The Python package stays as the readable reference implementation.

Status legend: ⬜ not started · 🟨 in progress · ✅ done

## Phase 0: Harden v0
| | Item | Why |
|---|---|---|
| ✅ | [#2] Durable witness storage (write-ahead log; fsync before every vote, release or freeze) | A witness that crashes and forgets a vote can equivocate. This is the top safety gap for real deployment |
| ✅ | [#3] Safe pledge release in wallets after a failed seal | Today a seal rejected before binding leaves the coin unusable |
| ✅ | [#4] Model checker: membership rotation and multiple constellations | Extend the adversarial search beyond one charter and one constellation |
| ✅ | [#5] Fuzz the holder-side validator | Malicious dossiers must only ever produce `InvalidDossier` |
| ✅ | [#6] TLA+ specification of the witness protocol, checked with TLC | Machine-checked safety theorem, with a mutation check to show the model catches bugs |
| ✅ | [#7] Deep confirmation (SPEC §9) implemented in the wallet | Detects long-range forgery by retired witnesses |

## Phase 1: Real network (#8)
| | Item |
|---|---|
| ✅ | Wire protocol v0: JSON over HTTP (`docs/WIRE.md`); binary encoding over HTTP/2 or QUIC moves to Phase 2 |
| ✅ | Witness server daemon with a durable store (`python -m sigil.witnessd`) |
| ✅ | Wallet CLI: keys, receive, pay, balance, dossier export and import (`python -m sigil.cli`) |
| ✅ | Gossip for charters and equivocation proofs (`sigil/gossip.py`) |
| ✅ | Multi-process local testnet and a SIGKILL crash/restart harness (`testnet/`); docker-compose written but not yet run |

## Phase 2: Performance, Rust (#9)
| | Item |
|---|---|
| ✅ | Rust witness: Ed25519 batch verification and an embedded key-value store (`rust/sigil-witness`; rotation, stamps and gossip storage still to port) |
| ⬜ | Sharding a witness's sigil space across machines |
| ✅ | Published benchmarks: votes/s per core, payment latency, dossier verification cost (`docs/BENCHMARKS.md`) |

## Phase 3: Dossier growth and privacy, research in parallel (#10)
| | Item |
|---|---|
| 🟨 | Recursive succinct proofs of ancestry validity: design and measurements in `docs/research/RECURSIVE_PROOFS.md`, toy Plonky2 recursive proof and RISC-V cycle counts in `research/`; full zkVM guest not yet built |
| 🟨 | Holder privacy: ancestry hidden behind proofs (designed in the same doc) |

## Phase 4: Missing features (#11)
| | Item |
|---|---|
| ⬜ | Constellation succession (dead-man takeover) |
| ⬜ | Arbiter objects for shared state (AMMs, auctions) |
| ⬜ | Issuer redemption: re-mint coins with short histories |
| ⬜ | Stamp pricing and bond sizing |

## Phase 5: Public testnet and audit (#12)
| | Item |
|---|---|
| ⬜ | Three or more independent constellations run by outside operators |
| ⬜ | Cryptography and protocol audit, then a v1 spec freeze |
