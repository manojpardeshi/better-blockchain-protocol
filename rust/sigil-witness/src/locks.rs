//! The lock language (SPEC §3.5): total predicates deciding who may consume a sigil.
//!
//! Mirrors `sigil/locks.py` exactly, including the node budget and the order in which
//! `all`/`any` short-circuit. Values must be well typed (strings are strings, integers are
//! integers and not booleans); where the reference would duck-type an odd value this
//! implementation answers `false`, which can only make a witness abstain.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::crypto::{decode_pk, decode_sig, hash_preimage, signing_message, verify_message};
use crate::json::{Json, Map};
use crate::model::unlock_message;
use crate::proofs::verify_equivocation;

pub const MAX_DEPTH: usize = 8;
pub const MAX_NODES: i64 = 64;

fn is_int(v: Option<&Json>) -> bool {
    matches!(v, Some(Json::Int(_)))
}

fn is_str(v: Option<&Json>) -> bool {
    matches!(v, Some(Json::Str(_)))
}

pub fn well_formed(lock: &Json) -> bool {
    let mut budget = MAX_NODES;
    wf(lock, 0, &mut budget)
}

fn wf(lock: &Json, depth: usize, budget: &mut i64) -> bool {
    *budget -= 1;
    let m = match lock {
        Json::Obj(m) if *budget >= 0 && depth <= MAX_DEPTH => m,
        _ => return false,
    };
    match m.get("op").and_then(Json::as_str) {
        Some("sig") => is_str(m.get("pk")) && m.len() == 2,
        Some("multi") => {
            let (Some(Json::Int(k)), Some(Json::Arr(pks))) = (m.get("k"), m.get("pks")) else {
                return false;
            };
            let mut seen: Vec<&str> = Vec::with_capacity(pks.len());
            for p in pks {
                match p {
                    Json::Str(s) => seen.push(s),
                    _ => return false,
                }
            }
            seen.sort_unstable();
            seen.dedup();
            *k >= 1 && *k <= pks.len() as i128 && seen.len() == pks.len() && m.len() == 3
        }
        Some("after" | "before") => is_int(m.get("t")) && m.len() == 2,
        Some("hash") => is_str(m.get("h")) && m.len() == 2,
        Some("equivocation") => is_str(m.get("witness")) && m.len() == 2,
        Some("all" | "any") => match m.get("of") {
            Some(Json::Arr(of)) if !of.is_empty() && m.len() == 2 => of.iter().all(|x| wf(x, depth + 1, budget)),
            _ => false,
        },
        Some("never") => m.len() == 1,
        _ => false,
    }
}

/// Every public key a lock could ask a signature from.
pub fn keys_in(lock: &Json) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(l: &Json, out: &mut Vec<String>) {
        match l.get("op").and_then(Json::as_str) {
            Some("sig") => out.extend(l.get("pk").and_then(Json::as_str).map(str::to_string)),
            Some("multi") => {
                for p in l.get("pks").and_then(Json::as_arr).into_iter().flatten() {
                    out.extend(p.as_str().map(str::to_string));
                }
            }
            Some("all" | "any") => {
                for x in l.get("of").and_then(Json::as_arr).into_iter().flatten() {
                    walk(x, out);
                }
            }
            _ => {}
        }
    }
    walk(lock, &mut out);
    out.sort();
    out.dedup();
    out
}

static EMPTY_MAP: std::sync::OnceLock<Map> = std::sync::OnceLock::new();

/// Is `lock` satisfied for consuming `sigil` in `tid`? `now = None` treats time conditions as
/// satisfied (holder re-check). `batch` lets equivocation proofs use batch verification.
pub fn evaluate(lock: &Json, unlock: &Json, sigil: &str, tid: &str, now: Option<i128>, batch: bool) -> bool {
    if !well_formed(lock) {
        return false;
    }
    let Json::Obj(u) = unlock else { return false };
    let empty = EMPTY_MAP.get_or_init(Map::new);
    let msg = signing_message("unlock", &unlock_message(sigil, tid, u.get("expires").cloned().unwrap_or(Json::Null)));
    let sigs = u.get("sigs").and_then(Json::as_obj).unwrap_or(empty);
    let preimages = u.get("preimages").and_then(Json::as_obj).unwrap_or(empty);
    let equivocations: &[Json] = u.get("equivocations").and_then(Json::as_arr).map(Vec::as_slice).unwrap_or(&[]);
    let ctx = Ctx { msg, sigs, preimages, equivocations, now, batch, cache: RefCell::new(HashMap::new()), equiv: RefCell::new(HashMap::new()) };
    ctx.ev(lock)
}

struct Ctx<'a> {
    msg: Vec<u8>,
    sigs: &'a Map,
    preimages: &'a Map,
    equivocations: &'a [Json],
    now: Option<i128>,
    batch: bool,
    cache: RefCell<HashMap<&'a str, bool>>,
    // Per witness key: does some proof convict it? Without this every `equivocation` node
    // re-verifies every proof, (nodes x proofs) signature checks per request.
    equiv: RefCell<HashMap<String, bool>>,
}

impl<'a> Ctx<'a> {
    fn has_sig(&self, pk: &'a str) -> bool {
        if let Some(r) = self.cache.borrow().get(pk) {
            return *r;
        }
        let ok = match self.sigs.get(pk) {
            Some(Json::Str(s)) => match (decode_pk(pk), decode_sig(s)) {
                (Some(k), Some(sig)) => verify_message(&k, &self.msg, &sig),
                _ => false,
            },
            _ => false,
        };
        self.cache.borrow_mut().insert(pk, ok);
        ok
    }

    fn ev(&self, node: &'a Json) -> bool {
        let get = |k: &str| node.get(k);
        match get("op").and_then(Json::as_str).unwrap_or("never") {
            "sig" => self.has_sig(get("pk").and_then(Json::as_str).unwrap_or("")),
            "multi" => {
                let k = get("k").and_then(Json::as_int).unwrap_or(i128::MAX);
                let mut n = 0i128;
                for pk in get("pks").and_then(Json::as_arr).into_iter().flatten() {
                    if self.has_sig(pk.as_str().unwrap_or("")) {
                        n += 1;
                        if n >= k {
                            return true;
                        }
                    }
                }
                n >= k
            }
            "after" => self.now.map_or(true, |now| now >= get("t").and_then(Json::as_int).unwrap_or(i128::MAX)),
            "before" => self.now.map_or(true, |now| now < get("t").and_then(Json::as_int).unwrap_or(i128::MIN)),
            "hash" => {
                let h = get("h").and_then(Json::as_str).unwrap_or("");
                match self.preimages.get(h) {
                    Some(Json::Str(pre)) => hash_preimage(pre).is_some_and(|x| x == h),
                    _ => false,
                }
            }
            "equivocation" => {
                let w = get("witness");
                let key = w.and_then(Json::as_str); // well_formed: always a string
                if let Some(r) = key.and_then(|k| self.equiv.borrow().get(k).copied()) {
                    return r;
                }
                let r = self.equivocations.iter().any(|p| {
                    matches!(p.get("a"), Some(Json::Obj(_)))
                        && p.get("a").and_then(|a| a.get("witness")).is_some_and(|x| Some(x) == w)
                        && verify_equivocation(p, self.batch)
                });
                if let Some(k) = key {
                    self.equiv.borrow_mut().insert(k.to_string(), r);
                }
                r
            }
            "all" => get("of").and_then(Json::as_arr).is_some_and(|of| of.iter().all(|x| self.ev(x))),
            "any" => get("of").and_then(Json::as_arr).is_some_and(|of| of.iter().any(|x| self.ev(x))),
            _ => false, // "never"
        }
    }
}
