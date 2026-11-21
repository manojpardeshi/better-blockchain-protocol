"""Stamp wire values must use the same plain-hex spelling in both witnesses."""

import unittest

from sigil.stamps import StampMint, buy_stamp, parse_hex


class StampHexTests(unittest.TestCase):
    def test_sale_value_requires_plain_hex(self):
        self.assertEqual(parse_hex("aB01"), 0xAB01)
        for bad in ("", "0x10", "+10", "-10", " 10", "10 ", "1_0", "zz", 16, None):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                parse_hex(bad)

    def test_noncanonical_signature_does_not_redeem(self):
        mint = StampMint(1024)
        good = buy_stamp(mint.public, mint.sign_blinded)
        sig = good["sig"]
        for bad in ("0x" + sig, "+" + sig, " " + sig, sig[:2] + "_" + sig[2:]):
            with self.subTest(bad=bad[:8]):
                self.assertFalse(mint.redeem(dict(good, sig=bad)))
        self.assertTrue(mint.redeem(good))
        self.assertFalse(mint.redeem(good))


if __name__ == "__main__":
    unittest.main()
