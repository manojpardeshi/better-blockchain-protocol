//! Builders for owner-side objects (spend requests, votes, seals), for tests and benchmarks.
//! A real wallet lives in the Python reference (`sigil/wallet.py`).

use crate::charter::constellation_id;
use crate::crypto::KeyPair;
use crate::json::{obj, Json};
use crate::model::{sigil_of, transition_id, unlock_message, vote_payload};

pub fn sig_lock(pk: &str) -> Json {
    obj([("op", "sig".into()), ("pk", Json::str(pk))])
}

/// A genesis charter for `keys`: returns `(cid, registry json)`.
pub fn genesis(name: &str, keys: &[&KeyPair]) -> (String, Json) {
    let body = obj([
        ("name", Json::str(name)),
        ("version", Json::Int(0)),
        ("witnesses", Json::Arr(keys.iter().map(|k| Json::str(&k.pk)).collect())),
        ("prev", Json::Null),
    ]);
    let cid = constellation_id(&body);
    let chain = Json::Arr(vec![obj([("body", body), ("sigs", Json::Obj(Default::default()))])]);
    (cid.clone(), Json::Obj([(cid, chain)].into_iter().collect()))
}

/// A one-input SPEND request for a parcel `{home, sig(owner), salt}` at generation `gen`.
/// Returns `(request, sigil, tid)`.
pub fn spend_request(owner: &KeyPair, home: &str, salt: &str, gen: i128, expires: i128, memo: &str) -> (Json, String, String) {
    let lock = sig_lock(&owner.pk);
    let sigil = sigil_of(&Json::str(home), &lock, &Json::str(salt));
    // The witness only sees the body's hash; any 64-hex string stands in for it here.
    let body_hash = crate::crypto::digest("body", &Json::str(memo));
    let header = obj([
        ("inputs", Json::Arr(vec![Json::Arr(vec![Json::str(&sigil), Json::Int(gen)])])),
        ("body", Json::str(body_hash)),
    ]);
    let tid = transition_id(&header);
    let sig = owner.sign("unlock", &unlock_message(&sigil, &tid, Json::Int(expires)));
    let unlock = obj([
        ("sigs", Json::Obj([(owner.pk.clone(), Json::Str(sig))].into_iter().collect())),
        ("preimages", Json::Obj(Default::default())),
        ("equivocations", Json::Arr(vec![])),
        ("expires", Json::Int(expires)),
    ]);
    let req = obj([
        ("sigil", Json::str(&sigil)),
        ("header", header),
        ("home", Json::str(home)),
        ("lock", lock),
        ("salt", Json::str(salt)),
        ("unlock", unlock),
    ]);
    (req, sigil, tid)
}

/// A signed vote.
pub fn vote(k: &KeyPair, cid: &str, sigil: &str, gen: i128, tid: &str, time: i128) -> Json {
    let mut v = obj([
        ("constellation", Json::str(cid)),
        ("version", Json::Int(0)),
        ("witness", Json::str(&k.pk)),
        ("sigil", Json::str(sigil)),
        ("gen", Json::Int(gen)),
        ("tid", Json::str(tid)),
        ("time", Json::Int(time)),
    ]);
    let sig = k.sign("vote", &vote_payload(&v).expect("complete"));
    if let Json::Obj(m) = &mut v {
        m.insert("sig".into(), Json::Str(sig));
    }
    v
}

/// `model.seal_from_votes`.
pub fn seal_from_votes(votes: &[Json]) -> Json {
    let f = &votes[0];
    let pick = |k: &str| f.get(k).cloned().unwrap_or(Json::Null);
    obj([
        ("constellation", pick("constellation")),
        ("version", pick("version")),
        ("sigil", pick("sigil")),
        ("gen", pick("gen")),
        ("tid", pick("tid")),
        (
            "votes",
            Json::Arr(
                votes
                    .iter()
                    .map(|v| {
                        obj([
                            ("witness", v.get("witness").cloned().unwrap_or(Json::Null)),
                            ("time", v.get("time").cloned().unwrap_or(Json::Null)),
                            ("sig", v.get("sig").cloned().unwrap_or(Json::Null)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}
