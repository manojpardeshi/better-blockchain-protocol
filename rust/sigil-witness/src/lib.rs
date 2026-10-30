//! A Sigil v0 witness, wire-compatible with the Python reference in `sigil/`.
//!
//! * [`json`]: JSON values and the canonical encoding (byte-identical to the reference);
//! * [`crypto`]: domain-separated BLAKE2b-256 and Ed25519, with batch verification;
//! * [`model`], [`locks`], [`proofs`], [`charter`]: SPEC §3;
//! * [`witness`]: SPEC §5 (SPEND, RELEASE, STATUS, FREEZE, ADOPT);
//! * [`stamps`]: blind RSA-FDH stamps (SPEC §3.10);
//! * [`gossip`]: storage of gossiped charter chains, equivocation proofs and fork evidence;
//! * [`store`]: durable state with group commit;
//! * [`server`]: the v0 HTTP JSON wire protocol (docs/WIRE.md).

pub mod charter;
pub mod crypto;
pub mod gossip;
pub mod json;
pub mod locks;
pub mod model;
pub mod proofs;
pub mod server;
pub mod stamps;
pub mod store;
pub mod testkit;
pub mod witness;

pub use charter::Registry;
pub use crypto::KeyPair;
pub use json::Json;
pub use witness::Witness;

/// Load a key file written by `python -m sigil.witnessd keygen`: `{"seed": hex, "pk": hex}`.
pub fn load_key(path: &str) -> Result<KeyPair, String> {
    let text = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let v = json::parse(&text).map_err(|e| format!("{path}: {e}"))?;
    let seed = v.get("seed").and_then(Json::as_str).ok_or_else(|| format!("{path}: no seed"))?;
    let seed: [u8; 32] = crypto::decode_hex(seed)
        .and_then(|b| b.try_into().ok())
        .ok_or_else(|| format!("{path}: seed must be 32 bytes of hex"))?;
    let kp = KeyPair::from_seed(&seed);
    if let Some(pk) = v.get("pk") {
        if pk.as_str() != Some(kp.pk.as_str()) {
            return Err(format!("{path}: public key does not match seed"));
        }
    }
    Ok(kp)
}

/// Load a charter registry file `{cid: [charter, …]}`, verifying every chain.
pub fn load_registry(path: &str) -> Result<Registry, String> {
    let text = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let v = json::parse(&text).map_err(|e| format!("{path}: {e}"))?;
    Registry::from_json(&v)
}

/// Write `data` to `path` readable only by its owner (mode 0600), as the reference's
/// `_write_private` does for key files and the stamp key.
#[cfg(unix)]
pub fn write_private(path: &str, data: &[u8]) -> std::io::Result<()> {
    use std::io::Write;
    use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
    let mut f = std::fs::OpenOptions::new().write(true).create(true).truncate(true).mode(0o600).open(path)?;
    f.write_all(data)?;
    f.sync_all()?;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
}

#[cfg(not(unix))]
pub fn write_private(path: &str, data: &[u8]) -> std::io::Result<()> {
    std::fs::write(path, data)
}

/// The operator token in `path` that authorises `/v0/freeze` and `/v0/adopt` (trimmed).
pub fn load_admin_token(path: &str) -> Result<String, String> {
    let t = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let t = t.trim();
    if t.is_empty() {
        return Err(format!("{path}: empty admin token"));
    }
    Ok(t.to_string())
}
