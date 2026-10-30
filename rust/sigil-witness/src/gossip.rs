//! Gossip storage for charter chains, equivocation proofs and fork evidence (docs/WIRE.md).
//!
//! Mirrors the `GossipStore` of `sigil/gossip.py`, as a witness uses it: it shares the
//! witness's registry, so a verified rotation learned by gossip is served on `/v0/charters`
//! and used for proofs straight away. Nothing gossiped is trusted:
//!
//! * a chain is learned only if it verifies from the cid and extends the known chain (a chain
//!   with the same bodies but other signature subsets is the same chain); a chain that
//!   diverges is never adopted, and if both branches verify the divergence is kept as fork
//!   evidence (one item per constellation);
//! * a proof is kept only if it is a valid equivocation proof (SPEC §3.8) against a member of
//!   a charter version the registry knows, one per witness key, with only the signed vote
//!   fields;
//! * a fork is kept only if both branches verify against the shared prefix.
//!
//! Gossip state is not persisted: it can be learned again from peers. Items are kept in the
//! order they were admitted, so `/v0/proofs` lists them as the reference does.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::charter::{verify_chain, Registry};
use crate::json::{obj, Json, Map};
use crate::model::vote_payload;
use crate::proofs::verify_equivocation;

/// Equivocation proofs per message.
pub const MAX_PROOFS: usize = 64;
/// Fork evidence items per message.
pub const MAX_FORKS: usize = 16;
/// Constellations (charter chains) per message.
pub const MAX_CHARTERS: usize = 64;
/// Charter versions per chain.
pub const MAX_CHAIN: usize = 1024;
/// New constellations a store accepts by gossip (extensions of known ones are always
/// accepted), and fork evidence items it keeps.
pub const MAX_CONSTELLATIONS: usize = 10_000;

/// A registry that is copied only when gossip first changes it (copy on write), so a message
/// that teaches nothing costs no copy of the registry.
pub struct CowRegistry<'a> {
    base: &'a Arc<Registry>,
    owned: Option<Registry>,
}

impl<'a> CowRegistry<'a> {
    pub fn new(base: &'a Arc<Registry>) -> CowRegistry<'a> {
        CowRegistry { base, owned: None }
    }

    pub fn get(&self) -> &Registry {
        self.owned.as_ref().unwrap_or(self.base)
    }

    fn get_mut(&mut self) -> &mut Registry {
        if self.owned.is_none() {
            self.owned = Some((**self.base).clone());
        }
        self.owned.as_mut().expect("just set")
    }

    /// The changed registry, if anything was learned.
    pub fn into_changed(self) -> Option<Registry> {
        self.owned
    }
}

/// Verified equivocation proofs and fork evidence, in admission order.
#[derive(Debug)]
pub struct GossipStore {
    proofs: Vec<Json>,
    accused: HashMap<String, usize>,
    forks: Vec<Json>,
    forked: HashSet<String>,
    pub max_constellations: usize,
}

impl Default for GossipStore {
    fn default() -> Self {
        GossipStore {
            proofs: Vec::new(),
            accused: HashMap::new(),
            forks: Vec::new(),
            forked: HashSet::new(),
            max_constellations: MAX_CONSTELLATIONS,
        }
    }
}

/// Only the signed fields of a vote, plus its signature.
fn vote_copy(v: &Json) -> Option<Json> {
    let mut out = vote_payload(v)?;
    if let Json::Obj(m) = &mut out {
        m.insert("sig".into(), v.get("sig")?.clone());
    }
    Some(out)
}

/// `verify_fork`: two different charters for one version, both quorum-signed by the shared
/// prefix (which starts at the genesis of `constellation`).
pub fn verify_fork(f: &Json) -> bool {
    let (Some(cid), Some(prefix), Some(a), Some(b)) = (
        f.get("constellation").and_then(Json::as_str),
        f.get("prefix").and_then(Json::as_arr),
        f.get("a"),
        f.get("b"),
    ) else {
        return false;
    };
    let (Some(ab), Some(bb)) = (a.get("body"), b.get("body")) else { return false };
    if prefix.is_empty() || prefix.len() >= MAX_CHAIN || ab == bb {
        return false;
    }
    let branch = |x: &Json| {
        let mut c = prefix.clone();
        c.push(x.clone());
        verify_chain(cid, &c).is_ok()
    };
    branch(a) && branch(b)
}

/// `check_message`: shape and size checks for a gossip message (`Err` is `bad_request`).
pub fn check_message(msg: &Json) -> Result<(Map, Vec<Json>, Vec<Json>), String> {
    let Json::Obj(m) = msg else { return Err("gossip message must be an object".into()) };
    let charters = m.get("charters").cloned().unwrap_or(Json::Obj(Map::new()));
    let proofs = m.get("proofs").cloned().unwrap_or(Json::Arr(vec![]));
    let forks = m.get("forks").cloned().unwrap_or(Json::Arr(vec![]));
    let (Json::Obj(charters), Json::Arr(proofs), Json::Arr(forks)) = (charters, proofs, forks) else {
        return Err("charters must be an object, proofs and forks lists".into());
    };
    if charters.len() > MAX_CHARTERS {
        return Err(format!("at most {MAX_CHARTERS} charter chains per message"));
    }
    if charters.values().any(|c| !matches!(c, Json::Arr(a) if a.len() <= MAX_CHAIN)) {
        return Err(format!("charter chains must be lists of at most {MAX_CHAIN}"));
    }
    if proofs.len() > MAX_PROOFS {
        return Err(format!("at most {MAX_PROOFS} proofs per message"));
    }
    if forks.len() > MAX_FORKS {
        return Err(format!("at most {MAX_FORKS} forks per message"));
    }
    Ok((charters, proofs, forks))
}

impl GossipStore {
    pub fn proofs(&self) -> &[Json] {
        &self.proofs
    }

    pub fn forks(&self) -> &[Json] {
        &self.forks
    }

    /// Witness keys we hold a proof against.
    pub fn convicted(&self) -> HashSet<String> {
        self.accused.keys().cloned().collect()
    }

    /// `/v0/proofs`: `{proofs, forks}`.
    pub fn snapshot_json(&self) -> Json {
        obj([("proofs", Json::Arr(self.proofs.clone())), ("forks", Json::Arr(self.forks.clone()))])
    }

    /// `add_chain`: learn `chain` if it verifiably extends ours. True if we learned something.
    pub fn add_chain(&mut self, reg: &mut CowRegistry, cid: &str, chain: &Json) -> bool {
        let Some(chain) = chain.as_arr() else { return false };
        if chain.is_empty() || chain.len() > MAX_CHAIN {
            return false;
        }
        let known: Vec<Json> = reg.get().raw_chain(cid).to_vec();
        if known.is_empty() && reg.get().len() >= self.max_constellations {
            return false;
        }
        for i in 0..known.len().min(chain.len()) {
            let Some(body) = chain[i].get("body") else { return false };
            if Some(body) != known[i].get("body") {
                self.note_fork(cid, &known, chain, i);
                return false;
            }
        }
        if chain.len() <= known.len() {
            return false;
        }
        // Same bodies as ours: keep our (already verified) prefix, so a different but valid
        // signature subset is not mistaken for a fork.
        let mut full = known.clone();
        full.extend_from_slice(&chain[known.len()..]);
        match verify_chain(cid, &full) {
            Ok(verified) => {
                reg.get_mut().insert_verified(cid, full, verified);
                true
            }
            Err(_) => false,
        }
    }

    fn note_fork(&mut self, cid: &str, known: &[Json], chain: &[Json], i: usize) {
        if self.forked.contains(cid) || i == 0 || self.forks.len() >= self.max_constellations {
            return; // i == 0: a different genesis is a different cid, not a fork
        }
        if verify_chain(cid, &chain[..=i]).is_ok() {
            let f = obj([
                ("constellation", Json::str(cid)),
                ("prefix", Json::Arr(known[..i].to_vec())),
                ("a", known[i].clone()),
                ("b", chain[i].clone()),
            ]);
            self.forked.insert(cid.to_string());
            self.forks.push(f);
        }
    }

    /// `add_fork`: keep verified fork evidence (one per constellation).
    pub fn add_fork(&mut self, f: &Json) -> bool {
        let Some(cid) = f.get("constellation").and_then(Json::as_str) else { return false };
        if self.forked.contains(cid) || self.forks.len() >= self.max_constellations || !verify_fork(f) {
            return false;
        }
        let keep = obj(["constellation", "prefix", "a", "b"].map(|k| (k, f.get(k).cloned().unwrap_or(Json::Null))));
        self.forked.insert(cid.to_string());
        self.forks.push(keep);
        true
    }

    /// `add_proof`: keep a verified proof against a member of a charter we know (one per key).
    pub fn add_proof(&mut self, reg: &Registry, proof: &Json, batch: bool) -> bool {
        if !verify_equivocation(proof, batch) {
            return false;
        }
        let (Some(a), Some(b)) = (proof.get("a"), proof.get("b")) else { return false };
        let Some(pk) = a.get("witness").and_then(Json::as_str) else { return false };
        if self.accused.contains_key(pk) {
            return false;
        }
        // Only members of a known charter: proofs against throwaway keys convict nobody and
        // would let anyone grow the store for free.
        let (Some(cid), Some(version)) = (a.get("constellation").and_then(Json::as_str), a.get("version").and_then(Json::as_int)) else {
            return false;
        };
        match reg.charter(cid, version) {
            Some(c) if c.is_member(pk) => {}
            _ => return false,
        }
        let (Some(ca), Some(cb)) = (vote_copy(a), vote_copy(b)) else { return false };
        self.accused.insert(pk.to_string(), self.proofs.len());
        self.proofs.push(obj([("a", ca), ("b", cb)]));
        true
    }

    /// `merge`: admit everything verifiable in a gossip message; return the accepted counts.
    /// Charters first, so a proof against a member of a rotation in the same message counts.
    pub fn merge(&mut self, reg: &mut CowRegistry, msg: &Json, batch: bool) -> Result<Json, String> {
        let (charters, proofs, forks) = check_message(msg)?;
        let (mut nc, mut np, mut nf) = (0i128, 0i128, 0i128);
        for (cid, chain) in &charters {
            nc += self.add_chain(reg, cid, chain) as i128;
        }
        for f in &forks {
            nf += self.add_fork(f) as i128;
        }
        for p in &proofs {
            np += self.add_proof(reg.get(), p, batch) as i128;
        }
        Ok(obj([("charters", Json::Int(nc)), ("proofs", Json::Int(np)), ("forks", Json::Int(nf))]))
    }
}
