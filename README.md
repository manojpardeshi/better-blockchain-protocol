# Sigil: a chainless value protocol

> **Witnesses enforce *who* and *once*. Holders enforce *what*. Nothing is ordered.**

Sigil moves value among people who don't trust each other **without any of the machinery that blockchains are built from**. It isn't a faster chain, a DAG, or a new consensus algorithm. It starts from the observation that **a double-spend is a conflict over one coin, so it never needed a global order of all transactions**. Uniqueness per coin needs only quorum intersection, not consensus.

| Blockchains have | Sigil has instead |
|---|---|
| Blocks, a chain, a global ledger | **Nothing global.** Each coin (*parcel*) carries its own proof (*dossier*) |
| Miners or validators executing every transaction | **Blind witnesses** that only attest "this coin was consumed once, with its owner's signature" |
| Consensus, leaders, total order | **Quorum intersection** per coin, with no leader and no ordering |
| Global state replicated everywhere | **Holder-side validation**: the recipient verifies the history it is paid with |
| Probabilistic or delayed finality | **Deterministic finality in one round trip** |
| Mempool, fee auctions, MEV | **No blockspace, so no auction and no reordering.** Fees are blind, unlinkable **stamps** |
| One network-wide security assumption | **Per-holder trust policies** over competing **constellations** |
| Bridges between chains | **Per-parcel homes**: moving between constellations is an ordinary payment |
| Slashing via on-chain governance | **Slashing as a lock**: a bond is a parcel anyone can claim with an equivocation proof |
| Validators that could censor or steal | Witnesses that **can't see value** and **can't steal**, even all of them together |

Read the **[whitepaper](docs/WHITEPAPER.md)** for the reasoning and the **[specification](docs/SPEC.md)** for the exact rules.

## How it works in 30 seconds

```
parcel  = {home, asset, amount, lock, salt}       a unit of value
sigil   = H(home, lock, salt)                       its single-use id (no asset, no amount)
header  = {inputs: [(sigil, gen)…], body: H(body)}  all a witness ever sees
seal    = a quorum of witness votes "sigil → transition"
dossier = transitions + seals back to the asset's genesis, carried by the holder
```

1. Bob gives Alice a one-time address and picks which constellation the parcel lives in.
2. Alice signs a transition and sends **only its header** to each input's witnesses.
3. Each witness checks the lock and that it hasn't voted for a different spend of that sigil, then signs. One round trip; witnesses never talk to each other.
4. A quorum of votes is a **seal**, and the payment is final. Alice hands Bob the dossier, and Bob verifies conservation, signatures and seals locally.

If a counter-party in a multi-party transaction cheats, the honest side uses a **death proof** to *release* its inputs. If a witness cheats, its two signatures form an **equivocation proof** that anyone can use to claim its bond.

## Try it

Requires Python ≥ 3.10 and the `cryptography` package.

```bash
pip install cryptography
python3 examples/demo.py             # guided tour: payments, blindness, double-spend, swaps, timelocks, rotation
python3 -m unittest discover -v      # 100 tests, including fuzzing, model checking and a multi-process testnet
SIGIL_MODEL_SEEDS=3000 SIGIL_MODEL_STEPS=200 python3 -m unittest tests.test_model_check   # deeper search
```

```python
from sigil import Network, Wallet

net   = Network()
orion = net.create_constellation("orion", n=4)
lyra  = net.create_constellation("lyra",  n=7)

alice, bob = Wallet("alice", net, orion), Wallet("bob", net, lyra)
usd = alice.issue("USD", 1_000_000)     # an asset id is the hash of its genesis
alice.pay(bob, usd, 250)                # sealed in one round trip, verified by bob
assert bob.balance(usd) == 250
```

## CLI quickstart

A file-based wallet for a real network (`sigil/cli.py`). `directory.json` lists witness URLs per constellation (see [docs/WIRE.md](docs/WIRE.md)). Every command prints JSON.

```sh
S="python -m sigil.cli --directory directory.json"
$S --wallet alice init --home <cid>
$S --wallet bob   init --home <cid>
$S --wallet alice issue USD 1000                  # -> {"asset": "<id>", ...}
$S --wallet bob   address > bob-addr.json         # bob gives this to alice
$S --wallet alice pay bob-addr.json <id> 300 --out payment.json
$S --wallet bob   receive payment.json [--deep]   # verifies, then takes custody
$S --wallet bob   balance; $S --wallet bob assets; $S --wallet bob export-dossier
```

Payments are handed from holder to holder as files; no server stores them. Receiving the same payment twice is a no-op; a tampered or already-spent payment is rejected. **Back up the wallet directory**: it holds your key seeds and your dossier, and in Sigil the dossier is the money. There is no ledger to recover it from.

## Repository layout

| Path | What |
|---|---|
| `sigil/model.py` | Wire objects: parcels, sigils, transitions, votes, seals |
| `sigil/locks.py` | The lock predicate language (sig, multisig, time, hash, equivocation, and/or) |
| `sigil/witness.py` | The witness: spend, release, status, freeze/adopt |
| `sigil/store.py` | Crash-safe, append-only SQLite log of witness state |
| `sigil/proofs.py` | Seal, equivocation and death-proof verification |
| `sigil/validate.py` | Dossiers, trust policies and holder-side validation |
| `sigil/wallet.py` | Building, authorising and sealing transitions; receiving; recovery |
| `sigil/swap.py` | Atomic multi-party transitions across constellations |
| `sigil/charter.py` | Constellation charters and membership rotation |
| `sigil/stamps.py` | Blind RSA stamps for paying witnesses |
| `sigil/network.py` | In-process simulated network with fault injection |
| `tests/` | Payments, security, recovery, rotation, durability, deep confirmation, fuzzing, adversarial model checking |

## Status

This is a **research prototype**: a complete reference implementation of the v0 draft, with an in-process network simulation. It hasn't been audited and has no network transport yet. The whitepaper's [limits and open problems](docs/WHITEPAPER.md#10-limits-and-open-problems) section lists what is still unsolved: dossier growth (recursive proofs), shared-state applications, constellation succession, and formal verification.

MIT licensed.
