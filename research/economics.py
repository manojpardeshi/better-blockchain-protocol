#!/usr/bin/env python3
"""Evaluate operator-supplied stamp and bond assumptions; no protocol changes.

Usage: python3 research/economics.py scenario.json
All monetary inputs must use the same unit. See docs/ECONOMICS.md.
The quorum-intersection calculation applies only within one charter membership/version.
"""

import argparse
from decimal import Decimal, InvalidOperation
import json


def reject_duplicate_keys(pairs):
    """Keep a JSON typo from silently replacing an exposure or bond input."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def amount(value, name):
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        raise ValueError(f"{name} must be a non-negative number")
    try:
        result = Decimal(str(value))
    except InvalidOperation as exc:
        raise ValueError(f"{name} must be a non-negative number") from exc
    if not result.is_finite() or result < 0:
        raise ValueError(f"{name} must be a non-negative finite number")
    return result


def evaluate(scenario):
    if not isinstance(scenario, dict):
        raise ValueError("scenario must be an object")
    members = scenario.get("witnesses")
    if not isinstance(members, list) or not members:
        raise ValueError("witnesses must be a non-empty list")
    ids = [member.get("id") for member in members if isinstance(member, dict)]
    if (len(ids) != len(members)
            or any(not isinstance(i, str) or not i for i in ids)
            or len(set(ids)) != len(ids)):
        raise ValueError("each witness needs a unique non-empty id")

    n = len(members)
    f = (n - 1) // 3
    q = n - f
    intersection = 2 * q - n
    exposure = amount(scenario["max_concurrent_loss"], "max_concurrent_loss")
    bonds = []
    positive_bond_ids = set()
    for member in members:
        name = member["id"]
        bond = amount(member["assumed_collectible_bond"], f"{name}.assumed_collectible_bond")
        bond_id = member.get("bond_id")
        if bond_id is not None:
            if not isinstance(bond_id, str) or not bond_id.strip():
                raise ValueError(f"{name}.bond_id must be a non-empty string")
            bond_id = bond_id.strip()
        if bond > 0:
            if bond_id is None:
                raise ValueError(f"{name}.bond_id is required for a positive assumed_collectible_bond")
            if bond_id in positive_bond_ids:
                raise ValueError(f"duplicate positive bond_id: {bond_id}")
            positive_bond_ids.add(bond_id)
        bonds.append((bond, name))
    bonds.sort()
    collateral_floor = sum((b for b, _ in bonds[:intersection]), Decimal(0))

    rows = []
    for member in members:
        name = member["id"]
        paid = member.get("paid_stamp_gate")
        if not isinstance(paid, bool):
            raise ValueError(f"{name}.paid_stamp_gate must be a boolean")
        price = amount(member["stamp_price"], f"{name}.stamp_price")
        sale = amount(member["variable_sale_cost"], f"{name}.variable_sale_cost")
        spend = amount(member["variable_spend_cost"], f"{name}.variable_spend_cost")
        fixed = amount(member["allocated_fixed_cost_per_stamp"], f"{name}.allocated_fixed_cost_per_stamp")
        cost_floor = sale + spend + fixed
        effective_revenue = price if paid else Decimal(0)
        rows.append({"id": name, "paid_stamp_gate": paid, "stamp_price": str(price),
                     "estimated_cost_per_redeemed_stamp": str(cost_floor),
                     "effective_revenue_per_redeemed_stamp": str(effective_revenue),
                     "effective_margin_per_redeemed_stamp": str(effective_revenue - cost_floor),
                     "sale_is_open": not paid})

    return {
        "intersection_scope": "two conflicting quorum seals under one charter membership/version",
        "n": n, "f": f, "q": q, "minimum_quorum_intersection": intersection,
        "least_assumed_collectible_bonds": [name for _, name in bonds[:intersection]],
        "assumed_collectible_collateral_floor": str(collateral_floor),
        "max_concurrent_loss": str(exposure),
        "collateral_minus_exposure": str(collateral_floor - exposure),
        "stamp_rows": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scenario", help="JSON scenario file (see docs/ECONOMICS.md)")
    args = parser.parse_args()
    try:
        with open(args.scenario, encoding="utf-8") as file:
            scenario = json.load(file, object_pairs_hook=reject_duplicate_keys)
        print(json.dumps(evaluate(scenario), indent=2))
    except (KeyError, ValueError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
