//! Votes, seals, equivocation proofs and death proofs (SPEC §3.6, §3.8, §3.9).
//!
//! Mirrors `sigil/proofs.py`, with one deliberate difference: a seal's vote entries must be
//! exactly `{witness, time, sig}` (SPEC §3.6). The reference builds each vote as
//! `dict(common, **entry)`, so extra keys in an entry silently *override* the seal-level
//! `constellation`/`version`/`sigil`/`gen`/`tid`; a seal can then be assembled from votes for
//! other transitions (or another constellation) and still verify. This implementation refuses
//! such seals. See docs/BENCHMARKS.md, "Compatibility notes".

use std::collections::HashSet;

use crate::charter::{quorum, Charter, Registry};
use crate::crypto::{decode_pk, decode_sig, signing_message, verify_many, SigCheck};
use crate::json::{Json, Map};
use crate::model::{sigil_of, vote_payload};

/// A vote's signature check, if the vote is complete and its key and signature decode.
fn vote_check(v: &Json, charter: Option<&Charter>) -> Option<SigCheck> {
    let payload = vote_payload(v)?;
    let pk_str = v.get("witness")?.as_str()?;
    let pk = match charter.and_then(|c| c.keys.get(pk_str)) {
        Some(k) => *k,
        None => decode_pk(pk_str)?,
    };
    let sig = decode_sig(v.get("sig")?.as_str()?)?;
    Some(SigCheck { pk, msg: signing_message("vote", &payload), sig })
}

/// `verify_vote`: the vote's signature by its own `witness` key is valid.
pub fn verify_vote(v: &Json) -> bool {
    vote_check(v, None).is_some_and(|c| verify_many(&[c], false)[0])
}

/// `_counted_witnesses`: distinct, non-convicted members of one charter version with valid
/// votes. `None` means "not a consistent set of votes from a known charter" (the reference's
/// `(set(), None)`, or an exception it would turn into `False`).
pub fn counted_witnesses<'r>(
    votes: &[Json],
    registry: &'r Registry,
    convicted: &HashSet<String>,
    batch: bool,
) -> Option<(HashSet<String>, &'r Charter)> {
    let first = votes.first()?;
    let cid = first.get("constellation")?.as_str()?;
    let version = first.get("version")?.as_int()?;
    let charter = registry.charter(cid, version)?;
    // Candidates: the first vote of each distinct, eligible member; later duplicates are only
    // looked at if an earlier vote by the same key turns out invalid (as in the reference).
    let mut by_pk: Vec<(&str, Vec<&Json>)> = Vec::new();
    let mut index: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
    for v in votes {
        if v.get("constellation")?.as_str()? != cid || v.get("version")?.as_int()? != version {
            return None;
        }
        let pk = v.get("witness")?.as_str()?;
        if !charter.is_member(pk) || convicted.contains(pk) {
            continue;
        }
        match index.get(pk) {
            Some(&i) => by_pk[i].1.push(v),
            None => {
                index.insert(pk, by_pk.len());
                by_pk.push((pk, vec![v]));
            }
        }
    }
    let mut counted = HashSet::new();
    let mut checks = Vec::with_capacity(by_pk.len());
    let mut owners = Vec::with_capacity(by_pk.len());
    let mut retry = Vec::new();
    for (i, (_, vs)) in by_pk.iter().enumerate() {
        match vote_check(vs[0], Some(charter)) {
            Some(c) => {
                checks.push(c);
                owners.push(i);
            }
            None => retry.push(i),
        }
    }
    for (ok, i) in verify_many(&checks, batch).into_iter().zip(owners) {
        if ok {
            counted.insert(by_pk[i].0.to_string());
        } else {
            retry.push(i);
        }
    }
    for i in retry {
        let (pk, vs) = &by_pk[i];
        if vs[1..].iter().any(|v| vote_check(v, Some(charter)).is_some_and(|c| verify_many(&[c], false)[0])) {
            counted.insert(pk.to_string());
        }
    }
    Some((counted, charter))
}

const SEAL_COMMON: [&str; 5] = ["constellation", "version", "sigil", "gen", "tid"];

/// `votes_of_seal`, refusing entries that are not exactly `{witness, time, sig}`.
pub fn votes_of_seal(seal: &Json) -> Option<Vec<Json>> {
    let s = seal.as_obj()?;
    let mut common = Map::new();
    for k in SEAL_COMMON {
        common.insert(k.to_string(), s.get(k)?.clone());
    }
    let entries = s.get("votes")?.as_arr()?;
    let mut out = Vec::with_capacity(entries.len());
    for e in entries {
        let e = e.as_obj()?;
        if e.len() != 3 || !["witness", "time", "sig"].iter().all(|k| e.contains_key(*k)) {
            return None;
        }
        let mut v = common.clone();
        for (k, x) in e {
            v.insert(k.clone(), x.clone());
        }
        out.push(Json::Obj(v));
    }
    Some(out)
}

/// `verify_seal`: at least a quorum of distinct, non-convicted members voted for exactly the
/// seal's `(constellation, version, sigil, gen, tid)`.
pub fn verify_seal(seal: &Json, registry: &Registry, convicted: &HashSet<String>, batch: bool) -> bool {
    let Some(votes) = votes_of_seal(seal) else { return false };
    match counted_witnesses(&votes, registry, convicted, batch) {
        Some((counted, charter)) => counted.len() >= quorum(charter.witnesses.len()),
        None => false,
    }
}

/// `verify_equivocation`: two valid votes by one witness, same constellation, sigil and
/// generation, different transitions.
pub fn verify_equivocation(proof: &Json, batch: bool) -> bool {
    let (Some(a), Some(b)) = (proof.get("a"), proof.get("b")) else { return false };
    let same_str = |k: &str| matches!((a.get(k), b.get(k)), (Some(Json::Str(x)), Some(Json::Str(y))) if x == y);
    let same_gen = matches!((a.get("gen"), b.get("gen")), (Some(Json::Int(x)), Some(Json::Int(y))) if x == y);
    let differ = matches!((a.get("tid"), b.get("tid")), (Some(Json::Str(x)), Some(Json::Str(y))) if x != y);
    if !(same_str("witness") && same_str("constellation") && same_str("sigil") && same_gen && differ) {
        return false;
    }
    match (vote_check(a, None), vote_check(b, None)) {
        (Some(x), Some(y)) => verify_many(&[x, y], batch).iter().all(|ok| *ok),
        _ => false,
    }
}

/// `proves_dead`: does `proof` show that transition `tid` (with `header`) can never be sealed?
/// The evidence must come from the target sigil's home (SPEC §3.9).
pub fn proves_dead(header: &Json, tid: &str, proof: &Json, registry: &Registry, batch: bool) -> bool {
    proves_dead_inner(header, tid, proof, registry, batch).unwrap_or(false)
}

fn proves_dead_inner(header: &Json, tid: &str, proof: &Json, registry: &Registry, batch: bool) -> Option<bool> {
    let target = proof.get("sigil")?.as_str()?;
    let gen = proof.get("gen")?.as_int()?;
    let wanted = Json::Arr(vec![Json::str(target), Json::Int(gen)]);
    if !header.get("inputs")?.as_arr()?.iter().any(|x| *x == wanted) {
        return Some(false);
    }
    let p = proof.get("parcel")?;
    let home = p.get("home")?;
    if sigil_of(home, p.get("lock")?, p.get("salt")?) != target {
        return Some(false);
    }
    let home = home.as_str()?;
    let str_is = |v: &Json, k: &str, want: &str| v.get(k).and_then(Json::as_str) == Some(want);
    let other_tid = |v: &Json| v.get("tid").and_then(Json::as_str).is_some_and(|t| t != tid);
    match proof.get("kind")?.as_str()? {
        "seal" => {
            let seal = proof.get("seal")?;
            Some(
                str_is(seal, "sigil", target)
                    && seal.get("gen")?.as_int()? == gen
                    && other_tid(seal)
                    && str_is(seal, "constellation", home)
                    && verify_seal(seal, registry, &HashSet::new(), batch),
            )
        }
        "votes" => {
            let votes = proof.get("votes")?.as_arr()?;
            for v in votes {
                if !(str_is(v, "sigil", target)
                    && v.get("gen")?.as_int()? == gen
                    && other_tid(v)
                    && str_is(v, "constellation", home))
                {
                    return Some(false);
                }
            }
            let (counted, charter) = counted_witnesses(votes, registry, &HashSet::new(), batch)?;
            Some(counted.len() >= quorum(charter.witnesses.len()))
        }
        _ => Some(false),
    }
}
