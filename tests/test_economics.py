"""Checks the worksheet's quorum and cost arithmetic, not protocol safety."""

import unittest

from research.economics import evaluate


def member(name, bond, price="1", gate=True):
    row = {"id": name, "assumed_collectible_bond": bond,
           "paid_stamp_gate": gate, "stamp_price": price,
           "variable_sale_cost": "0.1", "variable_spend_cost": "0.2",
           "allocated_fixed_cost_per_stamp": "0.3"}
    if bond != "0":
        row["bond_id"] = f"bond-{name}"
    return row


class EconomicsWorksheetTests(unittest.TestCase):
    def test_uses_cheapest_quorum_intersection(self):
        result = evaluate({"max_concurrent_loss": "29", "witnesses": [
            member("a", "10"), member("b", "20"),
            member("c", "30"), member("d", "40")]})
        self.assertEqual((result["f"], result["q"], result["minimum_quorum_intersection"]), (1, 3, 2))
        self.assertIn("one charter membership/version", result["intersection_scope"])
        self.assertEqual(result["least_assumed_collectible_bonds"], ["a", "b"])
        self.assertEqual(result["collateral_minus_exposure"], "1")
        self.assertEqual(result["stamp_rows"][0]["estimated_cost_per_redeemed_stamp"], "0.6")
        self.assertEqual(result["stamp_rows"][0]["effective_revenue_per_redeemed_stamp"], "1")
        self.assertEqual(result["stamp_rows"][0]["effective_margin_per_redeemed_stamp"], "0.4")

    def test_open_sale_is_reported_even_with_nominal_price(self):
        result = evaluate({"max_concurrent_loss": "0", "witnesses": [member("a", "0", gate=False)]})
        row = result["stamp_rows"][0]
        self.assertTrue(row["sale_is_open"])
        self.assertEqual(row["stamp_price"], "1")
        self.assertEqual(row["effective_revenue_per_redeemed_stamp"], "0")
        self.assertEqual(row["effective_margin_per_redeemed_stamp"], "-0.6")

    def test_rejects_duplicate_members_and_negative_amounts(self):
        with self.assertRaisesRegex(ValueError, "unique"):
            evaluate({"max_concurrent_loss": "1", "witnesses": [member("a", "1"), member("a", "2")]})
        with self.assertRaisesRegex(ValueError, "non-negative"):
            evaluate({"max_concurrent_loss": "1", "witnesses": [member("a", "-1")]})

    def test_positive_bond_requires_nonempty_id(self):
        witness = member("a", "10")
        del witness["bond_id"]
        with self.assertRaisesRegex(ValueError, "a.bond_id is required"):
            evaluate({"max_concurrent_loss": "0", "witnesses": [witness]})
        witness["bond_id"] = "  "
        with self.assertRaisesRegex(ValueError, "a.bond_id must be a non-empty string"):
            evaluate({"max_concurrent_loss": "0", "witnesses": [witness]})

    def test_rejects_duplicate_positive_bond_ids(self):
        witnesses = [member("a", "10"), member("b", "20")]
        witnesses[1]["bond_id"] = " bond-a "
        with self.assertRaisesRegex(ValueError, "duplicate positive bond_id: bond-a"):
            evaluate({"max_concurrent_loss": "0", "witnesses": witnesses})

    def test_distinct_positive_bonds_and_zero_allocation(self):
        witnesses = [member("a", "10"), member("b", "20"),
                     member("c", "0"), member("d", "0")]
        witnesses[3]["bond_id"] = "bond-a"  # A shared bond is counted only for a.
        result = evaluate({"max_concurrent_loss": "5", "witnesses": witnesses})
        self.assertEqual(result["assumed_collectible_collateral_floor"], "0")
        self.assertEqual(result["least_assumed_collectible_bonds"], ["c", "d"])


if __name__ == "__main__":
    unittest.main()
