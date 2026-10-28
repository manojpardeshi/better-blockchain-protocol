//! Constellation charters and the registry of verified charter chains (SPEC §3.7).

use std::collections::HashMap;

use ed25519_dalek::VerifyingKey;

use crate::crypto::{decode_pk, digest, verify};
use crate::json::Json;

/// Byzantine witnesses tolerated by a constellation of size n.
pub fn faults(n: usize) -> usize {
    n.saturating_sub(1) / 3
}

/// Votes needed for a seal.
pub fn quorum(n: usize) -> usize {
    // At least one vote: an empty charter must never accept unsigned evidence (Python: q(0) = 1).
    (n - faults(n)).max(1)
}

pub fn charter_hash(body: &Json) -> String {
    digest("charter", body)
}

pub fn constellation_id(genesis_body: &Json) -> String {
    digest("constellation", genesis_body)
}

/// One verified charter version.
#[derive(Debug, Clone)]
pub struct Charter {
    pub body: Json,
    pub version: i128,
    /// The witness list as written (its length sets the quorum, as in `proofs.py`).
    pub witnesses: Vec<String>,
    /// Decoded member keys (members whose key does not decode can never sign anything).
    pub keys: HashMap<String, VerifyingKey>,
}

impl Charter {
    fn from_body(body: &Json) -> Result<Charter, String> {
        let version = body.get("version").and_then(Json::as_int).ok_or("charter version must be an integer")?;
        let ws = body.get("witnesses").and_then(Json::as_arr).ok_or("charter witnesses must be a list")?;
        let mut witnesses = Vec::with_capacity(ws.len());
        for w in ws {
            witnesses.push(w.as_str().ok_or("witness keys must be strings")?.to_string());
        }
        let mut unique: Vec<&str> = witnesses.iter().map(String::as_str).collect();
        unique.sort_unstable();
        unique.dedup();
        if witnesses.is_empty() || unique.len() != witnesses.len() {
            return Err("charter witnesses must be non-empty and unique".into());
        }
        let keys = witnesses.iter().filter_map(|w| decode_pk(w).map(|k| (w.clone(), k))).collect();
        Ok(Charter { body: body.clone(), version, witnesses, keys })
    }

    pub fn is_member(&self, pk: &str) -> bool {
        self.witnesses.iter().any(|w| w == pk)
    }
}

/// `charter.verify_chain`: a list of `{"body", "sigs"}` charters, version 0 first.
pub fn verify_chain(cid: &str, chain: &[Json]) -> Result<Vec<Charter>, String> {
    let first = chain.first().ok_or("empty chain")?;
    let fb = first.get("body").ok_or("charter without body")?;
    if fb.get("version").and_then(Json::as_int) != Some(0) {
        return Err("chain must start at version 0".into());
    }
    if !fb.get("prev").is_some_and(Json::is_null) || constellation_id(fb) != cid {
        return Err("genesis charter does not match the constellation id".into());
    }
    let mut out = vec![Charter::from_body(fb)?];
    for pair in chain.windows(2) {
        let pb = pair[0].get("body").ok_or("charter without body")?;
        let cb = pair[1].get("body").ok_or("charter without body")?;
        let pv = pb.get("version").and_then(Json::as_int).ok_or("bad version")?;
        if cb.get("version").and_then(Json::as_int) != Some(pv + 1) {
            return Err("charter versions must be consecutive".into());
        }
        if cb.get("prev").and_then(Json::as_str) != Some(charter_hash(pb).as_str()) {
            return Err("charter does not extend its predecessor".into());
        }
        let prev = out.last().expect("non-empty");
        let mut members: Vec<&str> = prev.witnesses.iter().map(String::as_str).collect();
        members.sort_unstable();
        members.dedup(); // Python: set(pb["witnesses"])
        let sigs = pair[1].get("sigs").and_then(Json::as_obj).ok_or("charter sigs must be an object")?;
        let signers = sigs
            .iter()
            .filter(|(pk, sig)| {
                members.binary_search(&pk.as_str()).is_ok()
                    && sig.as_str().is_some_and(|s| verify(pk, "charter", cb, s))
            })
            .count();
        if signers < quorum(members.len()) {
            return Err("charter lacks a quorum of its predecessor's signatures".into());
        }
        out.push(Charter::from_body(cb)?);
    }
    Ok(out)
}

/// The charters a participant knows about, verified on entry.
#[derive(Debug, Default, Clone)]
pub struct Registry {
    raw: HashMap<String, Vec<Json>>,
    chains: HashMap<String, Vec<Charter>>,
}

impl Registry {
    /// Load a charter registry file `{cid: [charter, …]}` (docs/WIRE.md); any invalid chain is fatal.
    pub fn from_json(v: &Json) -> Result<Registry, String> {
        let m = v.as_obj().ok_or("registry must be an object")?;
        let mut reg = Registry::default();
        for (cid, chain) in m {
            let chain = chain.as_arr().ok_or("a chain must be a list")?;
            reg.add_chain(cid, chain).map_err(|e| format!("invalid charter chain for {}: {e}", short(cid)))?;
        }
        Ok(reg)
    }

    /// `Registry.add_chain`: ignores chains no longer than the known one, refuses forks.
    pub fn add_chain(&mut self, cid: &str, chain: &[Json]) -> Result<(), String> {
        let known = self.raw.get(cid).map(Vec::len).unwrap_or(0);
        if chain.len() <= known {
            return Ok(());
        }
        let verified = verify_chain(cid, chain)?;
        if let Some(k) = self.raw.get(cid) {
            if chain[..k.len()] != k[..] {
                return Err("charter fork".into());
            }
        }
        self.raw.insert(cid.to_string(), chain.to_vec());
        self.chains.insert(cid.to_string(), verified);
        Ok(())
    }

    pub fn charter(&self, cid: &str, version: i128) -> Option<&Charter> {
        let chain = self.chains.get(cid)?;
        usize::try_from(version).ok().and_then(|v| chain.get(v))
    }

    pub fn chain(&self, cid: &str) -> &[Charter] {
        self.chains.get(cid).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn contains(&self, cid: &str) -> bool {
        self.chains.contains_key(cid)
    }

    /// Every chain as served on `/v0/charters`.
    pub fn to_json(&self) -> Json {
        Json::Obj(self.raw.iter().map(|(k, v)| (k.clone(), Json::Arr(v.clone()))).collect())
    }
}

pub fn short(s: &str) -> &str {
    s.char_indices().nth(12).map(|(i, _)| &s[..i]).unwrap_or(s)
}
