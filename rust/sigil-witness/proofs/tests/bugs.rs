//! Bugs found while verifying the Rust witness (docs/VERIFY_RUST.md, "Bugs found"), all fixed.
//! Each test asserts the correct behaviour and failed on the code before its fix; they now run
//! as regression tests (`cargo test --release --test bugs`, also run in CI).

use std::sync::atomic::AtomicI64;
use std::sync::Arc;
use std::time::Instant;

use sigil_witness::charter::Registry;
use sigil_witness::crypto::digest;
use sigil_witness::json::{obj, parse, Json, Map};
use sigil_witness::locks::evaluate;
use sigil_witness::model::{sigil_of, transition_id};
use sigil_witness::proofs::{proves_dead, verify_seal};
use sigil_witness::store::Store;
use sigil_witness_proofs::checker::open_witness;
use sigil_witness_proofs::world::{default_headers, signed_vote, World, NOW};

/// BUG 1 (json.rs `Parser::hex4`): a `\u` escape whose four "hex digits" run into a multi-byte
/// UTF-8 character slices a `str` off a char boundary and panics. Reachable from every HTTP
/// request body (`server::call` parses before anything else).
#[test]
// Was BUG 1 (fixed): json::parse panics on a \\u escape followed by non-ASCII bytes
fn bug1_parser_panics_on_unicode_after_backslash_u() {
    for input in ["\"\\u111\u{e9}\"", "\"\\u\u{20ac}\u{e9}\"", "{\"request\":\"\\u1\u{e9}\u{e9}\"}"] {
        let r = std::panic::catch_unwind(|| parse(input.as_bytes()).is_err());
        assert_eq!(r.ok(), Some(true), "parse must return an error, not panic, on {input:?}");
    }
}

/// BUG 2 (charter.rs `faults`/`quorum`): for an empty witness list Rust computes q = 0, the
/// spec's floor((n-1)/3) (and Python's `(n - 1) // 3`) gives f = -1, q = 1. With a registered
/// constellation whose charter lists no witnesses, any seal or death proof "from" it verifies
/// with zero valid votes, and a successor charter needs zero signatures.
#[test]
// Was BUG 2 (fixed): quorum(0) is 0 (spec and reference: 1), so empty charters accept unsigned seals
fn bug2_empty_charter_accepts_unsigned_evidence() {
    let body = obj([("name", Json::str("E")), ("version", Json::Int(0)), ("witnesses", Json::Arr(vec![])), ("prev", Json::Null)]);
    let cid = sigil_witness::charter::constellation_id(&body);
    let reg_json = Json::Obj([(cid.clone(), Json::Arr(vec![obj([("body", body), ("sigs", Json::Obj(Map::new()))])]))].into_iter().collect());
    assert_eq!(sigil_witness::charter::quorum(0), 1, "quorum(0) per SPEC §7 (f = floor(-1/3) = -1)");
    // The fix refuses empty charters outright; if one ever loads, its evidence must still fail.
    let Ok(reg) = Registry::from_json(&reg_json) else { return };
    let lock = obj([("op", "never".into())]);
    let salt = Json::str("x");
    let s = sigil_of(&Json::str(&cid), &lock, &salt);
    let header = obj([("inputs", Json::Arr(vec![Json::Arr(vec![Json::str(&s), Json::Int(0)])])), ("body", Json::str("b"))]);
    let tid = transition_id(&header);
    let k = sigil_witness::crypto::KeyPair::from_seed(&[7; 32]); // not a member of anything
    let v = signed_vote(&k, &cid, 0, &s, 0, "other", 1);
    let seal = obj([
        ("constellation", Json::str(&cid)),
        ("version", Json::Int(0)),
        ("sigil", Json::str(&s)),
        ("gen", Json::Int(0)),
        ("tid", Json::str("other")),
        ("votes", Json::Arr(vec![obj([("witness", v.get("witness").unwrap().clone()), ("time", Json::Int(1)), ("sig", Json::str("00"))])])),
    ]);
    assert!(!verify_seal(&seal, &reg, &Default::default(), false), "a seal with no member votes must not verify");
    let proof = obj([
        ("kind", Json::str("votes")),
        ("sigil", Json::str(&s)),
        ("gen", Json::Int(0)),
        ("parcel", obj([("home", Json::str(&cid)), ("lock", lock), ("salt", salt)])),
        ("votes", Json::Arr(vec![v])),
    ]);
    assert!(!proves_dead(&header, &tid, &proof, &reg, false), "a death proof with no member votes must not verify");
}

/// BUG 5 (json.rs `py_float_repr`): when two shortest digit strings round-trip to the same
/// double and are exactly equally close to it, Python's `repr` picks the even last digit
/// (David Gay's dtoa, round-half-even) and Rust's `{:e}` picks the other one, so the canonical
/// encoding (and every hash over it: sigil, tid) differs from the reference. Found by the
/// canonical differential (proofs/diff/differential.py --canonical): 5 of 39,725 accepted texts.
/// Expected values are Python 3's `repr(float(text))`.
#[test]
// Was BUG 5 (fixed): py_float_repr breaks exact ties differently from Python repr (half-even)
fn bug5_float_repr_tie_breaking_differs_from_python() {
    let cases = [
        ("1966098015293243369E-3", "1966098015293243.2"),
        ("-591658828404238278E-3", "-591658828404238.2"),
        ("-80990177648277630E-3", "-80990177648277.62"),
        ("269733205174358640E-3", "269733205174358.62"),
        ("92926342307573118E-3", "92926342307573.12"),
    ];
    for (text, python) in cases {
        let v = parse(text.as_bytes()).expect("parses");
        assert_eq!(v.canonical_string(), python, "canonical form of {text}");
    }
}

/// BUG 6 (store.rs `load`): the reference now persists `frozen` as the hash of the successor
/// charter the witness froze for (sigil/store.py, commit fc8a82b; `true` only in older stores),
/// and the Rust store mirrors the reference's entry kinds. The Rust loader treats only `true`
/// as frozen, so a store holding the new form would restart UNFROZEN and vote again. Latent
/// today (the Rust witness never freezes), but it fails open, and must be fixed before FREEZE
/// is ported.
#[test]
// Was BUG 6 (fixed): a store whose `frozen` entry is a successor hash (reference format) loads as not frozen
fn bug6_frozen_successor_hash_loads_as_not_frozen() {
    let dir = std::env::temp_dir().join(format!("sigil-bug6-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("w.redb");
    let _ = std::fs::remove_file(&path);
    let (store, _) = Store::open(&path).unwrap();
    let seq = store.submit(vec![("frozen".into(), String::new(), Json::str("ab".repeat(32)))]);
    store.wait(seq);
    store.close();
    drop(store);
    let (store, loaded) = Store::open(&path).unwrap();
    let world = World::new(&default_headers());
    let w = open_witness(&world, store.clone(), loaded, Arc::new(AtomicI64::new(NOW as i64)));
    let frozen = w.frozen();
    let (r, _) = w.spend(&world.spend_request(0, 0, true, false));
    store.close();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(frozen, "a witness that froze for a successor must restart frozen");
    assert!(r.is_err(), "a frozen witness must not vote: {r:?}");
}

fn nested(depth: usize) -> Json {
    let mut v = Json::Int(0);
    for _ in 0..depth {
        v = Json::Arr(vec![v]);
    }
    v
}

fn max_depth(v: &Json) -> usize {
    match v {
        Json::Arr(a) => 1 + a.iter().map(max_depth).max().unwrap_or(0),
        Json::Obj(m) => 1 + m.values().map(max_depth).max().unwrap_or(0),
        _ => 0,
    }
}

/// BUG 3 (witness.rs + store.rs + json.rs MAX_DEPTH): a SPEND request is accepted when its body
/// nests up to 256 levels, and its authorisation (salt, header, unlock) is stored in the record's
/// log two levels deeper. The record is written fine, but on the next start `Store::open` parses
/// it with the same 256 limit, fails ("corrupt store value: nesting too deep") and the witness
/// refuses to start. Any owner of any parcel homed here can do this with one request (the salt
/// is theirs to choose), so every witness of a constellation can be bricked until an operator
/// repairs its store by hand.
#[test]
// Was BUG 3 (fixed): a deeply nested (but accepted) SPEND makes the store unloadable after restart
fn bug3_deep_request_bricks_the_store_on_restart() {
    let world = World::new(&default_headers());
    let owner = &world.owner;
    let lock = obj([("op", "sig".into()), ("pk", Json::str(&owner.pk))]);
    let home = Json::str(world.cid(0));
    // body = {"request": {.., "salt": S}}: S's subtree may nest 254 more levels (body depth 256).
    let salt = nested(254);
    let sigil = sigil_of(&home, &lock, &salt);
    let header = obj([("inputs", Json::Arr(vec![Json::Arr(vec![Json::str(&sigil), Json::Int(0)])])), ("body", Json::str(digest("body", &Json::Int(9))))]);
    let tid = transition_id(&header);
    let sig = owner.sign("unlock", &sigil_witness::model::unlock_message(&sigil, &tid, Json::Int(5000)));
    let unlock = obj([("sigs", Json::Obj([(owner.pk.clone(), Json::Str(sig))].into_iter().collect())), ("expires", Json::Int(5000))]);
    let req = obj([("sigil", Json::str(&sigil)), ("header", header), ("home", home), ("lock", lock), ("salt", salt), ("unlock", unlock)]);
    let body = obj([("request", req)]);
    assert_eq!(max_depth(&body), 256);
    let wire = body.canonical();
    let parsed = parse(&wire).expect("the server accepts this body");

    let dir = std::env::temp_dir().join(format!("sigil-bug3-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("w.redb");
    let _ = std::fs::remove_file(&path);
    let (store, loaded) = Store::open(&path).unwrap();
    let clock = Arc::new(AtomicI64::new(NOW as i64));
    let w = open_witness(&world, store.clone(), loaded, clock);
    let (r, seq) = w.spend(parsed.get("request").unwrap());
    assert!(r.is_ok(), "the witness votes: {r:?}");
    store.wait(seq);
    store.close();
    drop(w);
    drop(store);
    let reopened = Store::open(&path).map(|_| ());
    let _ = std::fs::remove_dir_all(&dir);
    assert!(reopened.is_ok(), "a witness must be able to restart on its own store: {:?}", reopened.err());
}

/// BUG 4 (locks.rs `Ctx::ev`, "equivocation"): every `equivocation` node re-verifies every
/// equivocation proof in the unlock (two Ed25519 checks, plus a failed batch check, per proof),
/// so the work is (#nodes x #proofs), not (#proofs). A lock of 63 such nodes and a 1 MiB unlock
/// costs tens of seconds of CPU per request, and SPEND runs on the async worker threads (not
/// `spawn_blocking`), so a few such requests stall the whole witness. Anyone can choose such a
/// lock for their own parcel. The test checks that evaluation time does not scale with the node
/// count (63 nodes must cost well under 10x one node).
#[test]
// Was BUG 4 (fixed): equivocation-lock evaluation is O(nodes x proofs) signature checks (CPU DoS)
fn bug4_equivocation_lock_cost_scales_with_nodes() {
    let world = World::new(&default_headers());
    let w = sigil_witness::crypto::KeyPair::from_seed(&[3; 32]);
    let node = obj([("op", "equivocation".into()), ("witness", Json::str(&w.pk))]);
    let mut bad = Vec::new();
    for i in 0..60 {
        // Cheap checks pass (same witness, constellation, sigil, gen; different tids), the
        // signatures do not verify.
        let mut a = signed_vote(&w, world.cid(0), 0, "s", 0, &format!("t{i}"), 1);
        let mut b = signed_vote(&w, world.cid(0), 0, "s", 0, &format!("u{i}"), 1);
        for v in [&mut a, &mut b] {
            if let Json::Obj(m) = v {
                m.insert("sig".into(), Json::str("11".repeat(64)));
            }
        }
        bad.push(obj([("a", a), ("b", b)]));
    }
    let unlock = obj([("sigs", Json::Obj(Map::new())), ("equivocations", Json::Arr(bad)), ("expires", Json::Int(0))]);
    let time = |n: usize| {
        let lock = obj([("op", "any".into()), ("of", Json::Arr(vec![node.clone(); n]))]);
        let t = Instant::now();
        assert!(!evaluate(&lock, &unlock, "s", "t", Some(0), true));
        t.elapsed().as_secs_f64()
    };
    let one = time(1);
    let many = time(63);
    eprintln!("1 node: {one:.4}s, 63 nodes: {many:.4}s, ratio {:.1}", many / one);
    assert!(many < 10.0 * one, "63 equivocation nodes cost {:.1}x one node", many / one);
}
