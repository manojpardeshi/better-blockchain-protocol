"""Checks the worksheet's quorum and cost arithmetic, not protocol safety."""

import unittest

from research.economics import evaluate


def member(name, bond, price="1", gate=True):
    return {"id": name, "assumed_collectible_bond": bond,
            "paid_stamp_gate": gate, "stamp_price": price,
            "variable_sale_cost": "0.1", "variable_spend_cost": "0.2",
            "allocated_fixed_cost_per_stamp": "0.3"}


class EconomicsWorksheetTests(unittest.TestCase):
    def test_uses_cheapest_quorum_intersection(self):
        result = evaluate({"max_concurrent_loss": "29", "witnesses": [
            member("a", "10"), member("b", "20"),
            member("c", "30"), member("d", "40")]})
        self.assertEqual((result["f"], result["q"], result["minimum_quorum_intersection"]), (1, 3, 2))
        self.assertEqual(result["least_assumed_collectible_bonds"], ["a", "b"])
        self.assertEqual(result["collateral_minus_exposure"], "1")
        self.assertEqual(result["stamp_rows"][0]["estimated_cost_per_redeemed_stamp"], "0.6")
        self.assertEqual(result["stamp_rows"][0]["price_minus_estimated_cost"], "0.4")

    def test_open_sale_is_reported_even_with_nominal_price(self):
        result = evaluate({"max_concurrent_loss": "0", "witnesses": [member("a", "0", gate=False)]})
        self.assertTrue(result["stamp_rows"][0]["sale_is_open"])

    def test_rejects_duplicate_members_and_negative_amounts(self):
        with self.assertRaisesRegex(ValueError, "unique"):
            evaluate({"max_concurrent_loss": "1", "witnesses": [member("a", "1"), member("a", "2")]})
        with self.assertRaisesRegex(ValueError, "non-negative"):
            evaluate({"max_concurrent_loss": "1", "witnesses": [member("a", "-1")]})


if __name__ == "__main__":
    unittest.main()
