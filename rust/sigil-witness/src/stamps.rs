//! Stamps (SPEC §3.10): blind RSA-FDH signatures that pay a witness for attention.
//!
//! Mirrors `sigil/stamps.py`. A witness sells stamps by blind-signing `FDH(serial)·rᵉ mod N`
//! (`/v0/sell_stamp`); a SPEND carries one stamp `{serial, sig}`, which the witness redeems
//! once. The witness never saw the serial it signed, so it cannot link a stamp to its buyer.
//!
//! The key file is the reference's: `{"n": hex, "e": hex, "d": hex}` (mode 0600), created on
//! first use and kept across restarts, so stamps sold before a restart stay valid. Redeemed
//! serials are part of the witness store (kind `stamp`).
//!
//! Hex parsing is stricter than Python's `int(x, 16)`: only `[0-9a-fA-F]+` is accepted (no sign,
//! `0x` prefix, underscores or whitespace). A stamp or blinded value written by the reference
//! (`format(x, "x")`) is always accepted; anything else is refused, which only makes the
//! witness refuse to sell or to vote.

use num_bigint_dig::{BigUint, ModInverse, RandPrime};
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::json::{obj, Json};

/// Public exponent of generated keys (as `cryptography`'s `generate_private_key`).
pub const PUBLIC_EXPONENT: u32 = 65537;

/// A stamp-signing RSA key.
pub struct StampKey {
    pub n: BigUint,
    pub e: BigUint,
    d: BigUint,
}

impl std::fmt::Debug for StampKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StampKey({} bits)", self.n.bits())
    }
}

/// `int(s, 16)` restricted to plain hex digits.
pub fn parse_hex(s: &str) -> Option<BigUint> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    BigUint::parse_bytes(s.as_bytes(), 16)
}

/// `format(x, "x")`.
pub fn to_hex(x: &BigUint) -> String {
    x.to_str_radix(16)
}

/// `full_domain_hash(n, serial)`: BLAKE2b-512 blocks of `"sigil/v0/stamp/{counter}/{serial}"`,
/// concatenated to `bytelen(n) + 16` bytes, read big-endian, reduced mod n.
pub fn full_domain_hash(n: &BigUint, serial: &str) -> BigUint {
    let size = n.bits().div_ceil(8) + 16;
    let mut out = Vec::with_capacity(size + 64);
    let mut counter = 0u64;
    while out.len() < size {
        let h = blake2b_simd::Params::new()
            .hash_length(64)
            .hash(format!("sigil/v0/stamp/{counter}/{serial}").as_bytes());
        out.extend_from_slice(h.as_bytes());
        counter += 1;
    }
    BigUint::from_bytes_be(&out[..size]) % n
}

impl StampKey {
    /// A key from its numbers, as the reference's `StampMint.from_numbers`.
    pub fn from_numbers(n: BigUint, e: BigUint, d: BigUint) -> Result<StampKey, String> {
        if n <= BigUint::one() || e.is_zero() || d.is_zero() {
            return Err("stamp key numbers out of range".into());
        }
        Ok(StampKey { n, e, d })
    }

    /// A fresh key of `bits` bits (`e = 65537`, `d = e⁻¹ mod lcm(p−1, q−1)`).
    pub fn generate(bits: usize) -> StampKey {
        let mut rng = rand::rngs::OsRng;
        let e = BigUint::from(PUBLIC_EXPONENT);
        loop {
            let p: BigUint = rng.gen_prime(bits / 2);
            let q: BigUint = rng.gen_prime(bits - bits / 2);
            if p == q {
                continue;
            }
            let n = &p * &q;
            if n.bits() != bits {
                continue;
            }
            let l = (&p - 1u32).lcm(&(&q - 1u32));
            let Some(d) = (&e).mod_inverse(&l).and_then(|d| d.to_biguint()) else { continue };
            return StampKey { n, e, d };
        }
    }

    /// `{n, e}` as served on `/v0/info` (hex strings).
    pub fn public_json(&self) -> Json {
        obj([("n", Json::str(to_hex(&self.n))), ("e", Json::str(to_hex(&self.e)))])
    }

    /// The private key file contents `{n, e, d}` (keep it secret).
    pub fn numbers_json(&self) -> Json {
        obj([("n", Json::str(to_hex(&self.n))), ("e", Json::str(to_hex(&self.e))), ("d", Json::str(to_hex(&self.d)))])
    }

    pub fn from_json(v: &Json) -> Result<StampKey, String> {
        let num = |k: &str| v.get(k).and_then(Json::as_str).and_then(parse_hex).ok_or_else(|| format!("stamp key: bad {k}"));
        StampKey::from_numbers(num("n")?, num("e")?, num("d")?)
    }

    /// `sign_blinded`: the blind signature `blindedᵈ mod n`; `Err` if `blinded` is not in `(0, n)`.
    pub fn sign_blinded(&self, blinded: &BigUint) -> Result<BigUint, String> {
        if blinded.is_zero() || *blinded >= self.n {
            return Err("blinded value out of range".into());
        }
        Ok(blinded.modpow(&self.d, &self.n))
    }

    /// `verify_stamp`: `0 < sig < n` and `sigᵉ ≡ FDH(serial) (mod n)`.
    pub fn verify(&self, stamp: &Json) -> bool {
        let (Some(serial), Some(sig)) = (stamp.get("serial").and_then(Json::as_str), stamp.get("sig").and_then(Json::as_str)) else {
            return false;
        };
        let Some(sig) = parse_hex(sig) else { return false };
        !sig.is_zero() && sig < self.n && sig.modpow(&self.e, &self.n) == full_domain_hash(&self.n, serial)
    }
}

/// Client side, for tests: blind `serial` with factor `r`, i.e. `FDH(serial)·rᵉ mod n`.
pub fn blind(key_n: &BigUint, key_e: &BigUint, serial: &str, r: &BigUint) -> BigUint {
    (full_domain_hash(key_n, serial) * r.modpow(key_e, key_n)) % key_n
}

/// Client side, for tests: `blind_sig · r⁻¹ mod n`.
pub fn unblind(key_n: &BigUint, blind_sig: &BigUint, r: &BigUint) -> Option<BigUint> {
    let inv = r.mod_inverse(key_n)?.to_biguint()?;
    Some((blind_sig * inv) % key_n)
}

/// `witnessd.load_mint`: the stamp key at `path`, created (mode 0600) on first use.
pub fn load_mint(path: &str, bits: usize) -> Result<StampKey, String> {
    match std::fs::read(path) {
        Ok(bytes) => {
            let v = crate::json::parse(&bytes).map_err(|e| format!("{path}: {e}"))?;
            StampKey::from_json(&v).map_err(|e| format!("{path}: {e}"))
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            let key = StampKey::generate(bits);
            crate::write_private(path, &key.numbers_json().canonical()).map_err(|e| format!("{path}: {e}"))?;
            Ok(key)
        }
        Err(e) => Err(format!("{path}: {e}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blind_sign_unblind_verify() {
        let key = StampKey::generate(512);
        let r = BigUint::from(123_456_789u64);
        let b = blind(&key.n, &key.e, "00ff", &r);
        let s = unblind(&key.n, &key.sign_blinded(&b).unwrap(), &r).unwrap();
        let stamp = obj([("serial", Json::str("00ff")), ("sig", Json::str(to_hex(&s)))]);
        assert!(key.verify(&stamp));
        let other = obj([("serial", Json::str("00fe")), ("sig", Json::str(to_hex(&s)))]);
        assert!(!key.verify(&other));
        assert!(key.sign_blinded(&BigUint::zero()).is_err());
        assert!(key.sign_blinded(&key.n).is_err());
        for bad in ["", "0x1", "-1", " 1", "zz"] {
            assert!(parse_hex(bad).is_none(), "{bad}");
        }
        let back = StampKey::from_json(&key.numbers_json()).unwrap();
        assert_eq!((back.n, back.e), (key.n.clone(), key.e.clone()));
        assert_eq!(key.n.bits(), 512);
    }
}
