//! Domain-separated BLAKE2b-256 hashing and Ed25519 signatures (SPEC §2).
//!
//! * `H(tag, x)   = BLAKE2b-256("sigil/v0/" ‖ tag ‖ 0x00 ‖ enc(x))`
//! * `Sig(tag, x) = Ed25519("sigil/v0/sig/" ‖ tag ‖ 0x00 ‖ enc(x))`

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

use crate::json::Json;

pub const DOMAIN: &[u8] = b"sigil/v0/";

fn blake2b256() -> blake2b_simd::State {
    blake2b_simd::Params::new().hash_length(32).to_state()
}

/// `H(tag, obj)` as lowercase hex.
pub fn digest(tag: &str, obj: &Json) -> String {
    digest_canonical(tag, &obj.canonical())
}

/// `H(tag, ·)` over bytes that are already canonical.
pub fn digest_canonical(tag: &str, canonical: &[u8]) -> String {
    let mut h = blake2b256();
    h.update(DOMAIN);
    h.update(tag.as_bytes());
    h.update(&[0]);
    h.update(canonical);
    h.finalize().to_hex().to_string()
}

/// Hash used by hash locks: BLAKE2b-256 of the raw preimage bytes, or `None` if not hex.
pub fn hash_preimage(preimage_hex: &str) -> Option<String> {
    let bytes = decode_hex(preimage_hex)?;
    let mut h = blake2b256();
    h.update(&bytes);
    Some(h.finalize().to_hex().to_string())
}

pub fn signing_message(tag: &str, obj: &Json) -> Vec<u8> {
    let body = obj.canonical();
    let mut m = Vec::with_capacity(DOMAIN.len() + 4 + tag.len() + 1 + body.len());
    m.extend_from_slice(DOMAIN);
    m.extend_from_slice(b"sig/");
    m.extend_from_slice(tag.as_bytes());
    m.push(0);
    m.extend_from_slice(&body);
    m
}

/// Hex decoding as Python's `bytes.fromhex` for the common case: either case, even length.
/// (Python additionally skips ASCII whitespace; refusing it only makes us stricter.)
pub fn decode_hex(s: &str) -> Option<Vec<u8>> {
    hex::decode(s).ok()
}

pub fn decode_pk(pk: &str) -> Option<VerifyingKey> {
    let b: [u8; 32] = decode_hex(pk)?.try_into().ok()?;
    VerifyingKey::from_bytes(&b).ok()
}

pub fn decode_sig(sig: &str) -> Option<Signature> {
    let b: [u8; 64] = decode_hex(sig)?.try_into().ok()?;
    Some(Signature::from_bytes(&b))
}

/// Single-signature verification (cofactorless, canonical `s`, like OpenSSL used by Python).
pub fn verify_message(pk: &VerifyingKey, msg: &[u8], sig: &Signature) -> bool {
    pk.verify(msg, sig).is_ok()
}

/// `verify(pk, tag, obj, sig)` of the reference: false on any malformed input.
pub fn verify(pk: &str, tag: &str, obj: &Json, sig: &str) -> bool {
    match (decode_pk(pk), decode_sig(sig)) {
        (Some(k), Some(s)) => verify_message(&k, &signing_message(tag, obj), &s),
        _ => false,
    }
}

/// One signature to check, already decoded.
pub struct SigCheck {
    pub pk: VerifyingKey,
    pub msg: Vec<u8>,
    pub sig: Signature,
}

/// Which of `checks` are valid. With `batch`, first tries one Ed25519 batch verification of
/// all of them; if the batch fails (some signature is bad) every one is checked on its own,
/// so the answer per signature is the same as single verification for honestly formed
/// signatures. See docs/BENCHMARKS.md for the cost and the caveat on crafted signatures.
pub fn verify_many(checks: &[SigCheck], batch: bool) -> Vec<bool> {
    if batch && checks.len() > 1 {
        let msgs: Vec<&[u8]> = checks.iter().map(|c| c.msg.as_slice()).collect();
        let sigs: Vec<Signature> = checks.iter().map(|c| c.sig).collect();
        let keys: Vec<VerifyingKey> = checks.iter().map(|c| c.pk).collect();
        if ed25519_dalek::verify_batch(&msgs, &sigs, &keys).is_ok() {
            return vec![true; checks.len()];
        }
    }
    checks.iter().map(|c| verify_message(&c.pk, &c.msg, &c.sig)).collect()
}

/// An Ed25519 key pair; `pk` is the hex-encoded raw public key.
pub struct KeyPair {
    sk: SigningKey,
    pub pk: String,
}

impl KeyPair {
    /// From the 32-byte RFC 8032 seed (what `sigil.witnessd keygen` stores as `seed`).
    pub fn from_seed(seed: &[u8; 32]) -> KeyPair {
        let sk = SigningKey::from_bytes(seed);
        let pk = hex::encode(sk.verifying_key().as_bytes());
        KeyPair { sk, pk }
    }

    /// Python's `KeyPair.from_seed(seed)`: the private key is BLAKE2b-256(seed).
    pub fn from_py_seed(seed: &[u8]) -> KeyPair {
        let mut h = blake2b256();
        h.update(seed);
        let d: [u8; 32] = h.finalize().as_bytes().try_into().expect("32 bytes");
        KeyPair::from_seed(&d)
    }

    pub fn generate() -> (KeyPair, [u8; 32]) {
        let mut seed = [0u8; 32];
        rand::RngCore::fill_bytes(&mut rand::rngs::OsRng, &mut seed);
        (KeyPair::from_seed(&seed), seed)
    }

    pub fn verifying_key(&self) -> VerifyingKey {
        self.sk.verifying_key()
    }

    pub fn sign(&self, tag: &str, obj: &Json) -> String {
        hex::encode(self.sk.sign(&signing_message(tag, obj)).to_bytes())
    }
}

impl std::fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "KeyPair({}…)", &self.pk[..12])
    }
}
