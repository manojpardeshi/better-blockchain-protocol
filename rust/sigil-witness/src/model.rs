//! Wire objects (SPEC §3): sigils, transition ids, unlock messages, votes, seals.

use crate::crypto::digest;
use crate::json::{obj, Json};

/// `sigil(p) = H("sigil", {home, lock, salt})`. Any JSON values are hashed as given.
pub fn sigil_of(home: &Json, lock: &Json, salt: &Json) -> String {
    digest("sigil", &obj([("home", home.clone()), ("lock", lock.clone()), ("salt", salt.clone())]))
}

/// `tid = H("transition", header)`: the header is hashed exactly as received.
pub fn transition_id(header: &Json) -> String {
    digest("transition", header)
}

/// What a lock's signatures sign (tag "unlock"): consume `sigil` in `tid`, if bound by `expires`.
pub fn unlock_message(sigil: &str, tid: &str, expires: Json) -> Json {
    obj([("sigil", Json::str(sigil)), ("tid", Json::str(tid)), ("expires", expires)])
}

pub const VOTE_FIELDS: [&str; 7] = ["constellation", "version", "witness", "sigil", "gen", "tid", "time"];

/// The signed part of a vote: its seven fields, or `None` if any is missing.
pub fn vote_payload(v: &Json) -> Option<Json> {
    let m = v.as_obj()?;
    let mut out = crate::json::Map::new();
    for k in VOTE_FIELDS {
        out.insert(k.to_string(), m.get(k)?.clone());
    }
    Some(Json::Obj(out))
}
