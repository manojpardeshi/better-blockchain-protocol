# Stamp pricing and bond sizing worksheet

This is an operator worksheet, not a protocol parameter or a claim that a
constellation is economically secure. The v0 protocol specifies how stamps are
redeemed and how bonds can be locked, but leaves payment for stamps and bond
amounts to operators ([SPEC §3.10 and §5.6](SPEC.md), [SPEC §9](SPEC.md)).

`research/economics.py` checks two narrow conditions using **operator supplied**
numbers. Run it before deciding to accept a given value at a home, and rerun it
when prices, exposures, bond homes, auditors or costs change. Keep the scenario
and the evidence behind each input with the decision.

## What the worksheet calculates

For *n* members of **one charter version**, the protocol uses
*f* = floor((*n* − 1)/3) and *q* = *n* − *f*. Two conflicting quorum seals for
the same sigil and generation **under that same membership** share at least
`2q − n` signing witnesses. The worksheet sorts the assumed
collectible bond amounts and adds the cheapest `2q − n`. This is a **conditional
lower bound** on collateral associated with such a pair of seals. It compares
that number with a supplied `max_concurrent_loss`, the total value that could be
lost across all simultaneous exposures before a response, in one monetary unit.
An individual payment limit is insufficient if many payments can be attacked at
once. A positive difference is only a screen; it is not proof of deterrence or
recovery. Conflicting seals involving different charter memberships or versions,
including retired-key attacks, are outside this calculation.

For each witness, the worksheet adds the estimated variable cost of one stamp
sale, one redeemed SPEND, and an allocation of fixed cost per redeemed stamp.
It compares that sum with effective revenue per redeemed stamp. The
quoted `stamp_price` counts as revenue only when `paid_stamp_gate` is true.
The [current witness code](../sigil/witness.py)
redeems and persists a stamp **before** later SPEND validation, so rejected
attempts can consume stamps and cost resources. The [reference wallet](../sigil/wallet.py)
asks every member for a vote, consuming up to *n* stamps for a one input payment
when all members require them. Each witness sells its own stamps.

The public `/v0/sell_stamp` endpoint currently blind signs without collecting
payment ([WIRE admission control](WIRE.md)). Setting `paid_stamp_gate` to `false`
marks a witness as having zero effective revenue and a negative margin against a
caller who can ask for free stamps, regardless of the quoted `stamp_price`.
The worksheet does not
model network floods, invalid or reused stamps, Sybil addresses, or availability.
Rate limits and network controls remain necessary.

## Scenario file

List the witnesses of one charter version only. All amounts must use the
**same unit and valuation date**. `assumed_collectible_bond`
is an intentionally conservative amount: use zero when a bond is absent, expired,
homed in a compromised constellation, unavailable to the intended claimant, or
otherwise not demonstrably collectible. Do not enter a bond's face amount merely
because it exists. Give every positive amount a non-empty `bond_id` that identifies
the underlying bond parcel. A bond ID may have a positive amount on only one witness
row: if several witnesses share one bond, allocate its collectible amount to one
row and enter zero for the others. Zero rows may omit `bond_id` or repeat the
shared ID. Count separate positive amounts only when they are backed by genuinely
separate bond parcels with distinct IDs. The worksheet checks ID uniqueness, but
cannot verify that the parcels are independent or collectible. Record the bond
parcel, home, lock, unbond time, auditor independence and claim procedure outside
this file. The current auditor signed
lock prevents the original self claim bug, but the lock alone does not promise
that auditors sign, that a claim wins, or that victims receive the proceeds.

```json
{
  "max_concurrent_loss": "40",
  "witnesses": [
    {"id": "A", "bond_id": "bond-A", "assumed_collectible_bond": "25", "paid_stamp_gate": true,
     "stamp_price": "0.02", "variable_sale_cost": "0.002",
     "variable_spend_cost": "0.006", "allocated_fixed_cost_per_stamp": "0.004"},
    {"id": "B", "bond_id": "bond-B", "assumed_collectible_bond": "25", "paid_stamp_gate": true,
     "stamp_price": "0.02", "variable_sale_cost": "0.002",
     "variable_spend_cost": "0.006", "allocated_fixed_cost_per_stamp": "0.004"},
    {"id": "C", "bond_id": "bond-C", "assumed_collectible_bond": "25", "paid_stamp_gate": true,
     "stamp_price": "0.02", "variable_sale_cost": "0.002",
     "variable_spend_cost": "0.006", "allocated_fixed_cost_per_stamp": "0.004"},
    {"id": "D", "bond_id": "bond-D", "assumed_collectible_bond": "25", "paid_stamp_gate": true,
     "stamp_price": "0.02", "variable_sale_cost": "0.002",
     "variable_spend_cost": "0.006", "allocated_fixed_cost_per_stamp": "0.004"}
  ]
}
```

These are **toy inputs**, not recommended amounts or measured costs. For *n* = 4,
*q* = 3 and the minimum intersection is 2, so this example reports 50 of
assumed collectible collateral against 40 of maximum concurrent loss. A member's
illustrative stamp cost is 0.012 against a price of 0.02. The result does not
establish that 25 is an adequate bond or 0.02 is an adequate price.

Save the JSON as `scenario.json`, then run:

```sh
python3 research/economics.py scenario.json
```

## How to populate it with evidence

1. **Measure spend cost under load.** Use the existing benchmark as a starting
   point, but measure CPU time, durable write bytes, disk space, bandwidth and
   operational overhead on the actual host and workload, with stamps enabled.
   [BENCHMARKS.md](BENCHMARKS.md) measures votes with fresh one input payments
   and no stamp cost. Its single machine throughput numbers are not a cost per
   stamp. Include valid SPENDs, malformed requests with valid stamps, repeated
   requests, and storage growth over the intended retention period.
2. **Measure sale and payment cost.** Include RSA blind signing, payment processor
   charges, refunds or failed payments, and key operations. Only set
   `paid_stamp_gate` to `true` after the sale endpoint actually enforces payment
   before signing. There is no such gate in the reference daemon today.
3. **Allocate fixed cost.** Divide the operating cost you intend stamps to fund
   by a conservative count of paid, redeemed stamps over the same period. If
   expected demand is low, the allocation rises. The worksheet reports only a
   cost floor, not a demand curve or a spam resistant price.
4. **Set exposure.** Bound the total value that could be accepted under a
   conflicting seal before detection, halt and recovery. Include simultaneous
   payments across all homes that rely on the same bond and asset conversion at
   a stress valuation; document the horizon and independently enforce the limit.
   The repository currently has no
   automatic exposure meter or charter field publishing bonds.
5. **Audit collectibility.** Verify each bond's home, asset, lock, expiry,
   auditors and claim path. Haircut the amount for asset price moves, costs and
   uncertainty; use zero where the claim cannot be demonstrated. Check that
   every bond remains locked longer than the witness term plus the deep
   confirmation horizon, as [SPEC §9](SPEC.md) recommends.

## Limits that a passing worksheet cannot clear

* The quorum intersection applies to **two conflicting seals for one sigil and
  generation**. Charter forks, unavailable witnesses, unproved misconduct,
  key compromise, and long range forgery need separate analysis. Fork signatures
  do not unlock the present equivocation bond ([WIRE gossip](WIRE.md)).
* `assumed_collectible_bond` is an assumption about a successful independent
  claim, not an amount automatically transferred to a victim. A bond may be
  slashable yet have little deterrent effect if the attacker can recapture the
  proceeds or auditors cannot act in time.
* Pricing above measured cost may cover service expense but cannot guarantee
  availability. An attacker willing to pay, or one who can get stamps without
  paying, can still exhaust capacity. Non-SPEND calls do not require stamps.
* The worksheet does not set stamp denominations, quote currencies, refunds,
  exposure enforcement or risk tolerances. Those are deployment decisions that
  should be tested with independent operators before real value is accepted.
