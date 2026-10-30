//! Golden vectors produced by the Python reference (tests/gen_vectors.py).

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

use sigil_witness::charter::Registry;
use sigil_witness::crypto::{digest, verify, KeyPair};
use sigil_witness::json::{parse, parse_str, Json};
use sigil_witness::locks::{evaluate, well_formed};
use sigil_witness::model::{sigil_of, transition_id, unlock_message};
use sigil_witness::proofs::{proves_dead, verify_equivocation, verify_seal};
use sigil_witness::stamps::{full_domain_hash, StampKey};
use sigil_witness::store::Store;
use sigil_witness::witness::{Error, Witness};

fn vectors() -> Json {
    let text = std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/vectors.json")).expect("vectors.json");
    parse(&text).expect("vectors parse")
}

fn arr<'a>(v: &'a Json, k: &str) -> &'a Vec<Json> {
    v.get(k).and_then(Json::as_arr).unwrap_or_else(|| panic!("missing list {k}"))
}

fn s<'a>(v: &'a Json, k: &str) -> &'a str {
    v.get(k).and_then(Json::as_str).unwrap_or_else(|| panic!("missing string {k}"))
}

#[test]
fn canonical_encoding_and_digests() {
    let v = vectors();
    let cases = arr(&v, "canonical");
    assert!(cases.len() > 1000);
    for c in cases {
        let parsed = parse_str(s(c, "json")).unwrap_or_else(|e| panic!("{e}: {}", s(c, "json")));
        assert_eq!(parsed.canonical_string(), s(c, "canonical"), "input {}", s(c, "json"));
        assert_eq!(digest("test", &parsed), s(c, "digest"));
        // Canonical output re-parses to the same canonical output.
        assert_eq!(parse_str(s(c, "canonical")).unwrap().canonical_string(), s(c, "canonical"));
    }
}

#[test]
fn keys_and_signatures() {
    let v = vectors();
    for c in arr(&v, "keys") {
        let kp = KeyPair::from_py_seed(&hex::decode(s(c, "py_seed")).unwrap());
        assert_eq!(kp.pk, s(c, "pk"));
        let obj = c.get("obj").unwrap();
        assert_eq!(kp.sign("vote", obj), s(c, "sig"));
        assert!(verify(&kp.pk, "vote", obj, s(c, "sig")));
        assert!(!verify(&kp.pk, "unlock", obj, s(c, "sig")));
        let i = obj.get("i").and_then(Json::as_int).unwrap();
        let msg = unlock_message(&"s".repeat(64), &"t".repeat(64), Json::Int(1700000000 + i));
        assert_eq!(kp.sign("unlock", &msg), s(c, "unlock_sig"));
    }
}

#[test]
fn model_ids() {
    let v = vectors();
    for c in arr(&v, "model") {
        let p = c.get("parcel").unwrap();
        assert_eq!(sigil_of(p.get("home").unwrap(), p.get("lock").unwrap(), p.get("salt").unwrap()), s(c, "sigil"));
        assert_eq!(digest("body", c.get("body").unwrap()), s(c, "body_hash"));
        assert_eq!(transition_id(c.get("header").unwrap()), s(c, "tid"));
    }
}

#[test]
fn lock_evaluation() {
    let v = vectors();
    for (i, c) in arr(&v, "locks").iter().enumerate() {
        let lock = c.get("lock").unwrap();
        assert_eq!(Json::Bool(well_formed(lock)), *c.get("well_formed").unwrap(), "case {i}");
        for (now, want) in c.get("eval").and_then(Json::as_obj).unwrap() {
            let now = if now == "None" { None } else { Some(now.parse::<i128>().unwrap()) };
            for batch in [false, true] {
                let got = evaluate(lock, c.get("unlock").unwrap(), s(c, "sigil"), s(c, "tid"), now, batch);
                assert_eq!(Json::Bool(got), *want, "lock case {i} at {now:?}: {}", lock.canonical_string());
            }
        }
    }
}

fn expected(c: &Json) -> bool {
    c.get("rust").or_else(|| c.get("python")).unwrap() == &Json::Bool(true)
}

#[test]
fn seals_equivocations_and_death_proofs() {
    let v = vectors();
    let p = v.get("proofs").unwrap();
    let reg = Registry::from_json(p.get("registry").unwrap()).unwrap();
    for c in arr(p, "seals") {
        let convicted: HashSet<String> = c
            .get("convicted")
            .and_then(Json::as_arr)
            .map(|a| a.iter().filter_map(|x| x.as_str().map(str::to_string)).collect())
            .unwrap_or_default();
        for batch in [false, true] {
            assert_eq!(verify_seal(c.get("seal").unwrap(), &reg, &convicted, batch), expected(c), "seal {}", s(c, "name"));
        }
    }
    for c in arr(p, "equivocations") {
        for batch in [false, true] {
            assert_eq!(verify_equivocation(c.get("proof").unwrap(), batch), expected(c), "equivocation {}", s(c, "name"));
        }
    }
    for c in arr(p, "deaths") {
        for batch in [false, true] {
            let got = proves_dead(p.get("header").unwrap(), s(p, "tid"), c.get("proof").unwrap(), &reg, batch);
            assert_eq!(got, expected(c), "death proof {}", s(c, "name"));
        }
    }
}

/// Compare one call's outcome with the reference's recorded answer.
fn check_outcome(i: usize, step: &Json, got: Result<Json, Error>) {
    let want = step.get("expect").unwrap();
    match (got, want.get("error").and_then(Json::as_str)) {
        (Ok(x), None) => assert_eq!(
            x.canonical_string(),
            want.get("ok").unwrap().canonical_string(),
            "step {i} ({} {})",
            s(step, "op"),
            step.get("who").and_then(Json::as_str).unwrap_or("")
        ),
        (Err(Error::Conflict(vote)), Some("conflict")) => {
            assert_eq!(vote.unwrap_or(Json::Null), *want.get("vote").unwrap(), "step {i}")
        }
        (Err(Error::Rejected(m)), Some("rejected")) => assert_eq!(m, s(want, "message"), "step {i}"),
        (Err(Error::BadRequest(_)), Some("bad_request")) => {}
        (got, _) => panic!("step {i} ({}): got {got:?}, want {}", s(step, "op"), want.canonical_string()),
    }
}

/// Replay a multi-witness script (`Script` in gen_vectors.py): every witness is built as the
/// reference built it, every call must give the reference's answer, byte for byte.
fn replay_script(script: &Json, stamp_key: Option<&Json>) -> usize {
    let regs = script.get("registries").unwrap();
    let cid = s(script, "cid");
    let now = Arc::new(AtomicI64::new(0));
    let mut ws: HashMap<String, Witness> = HashMap::new();
    for (who, spec) in script.get("witnesses").and_then(Json::as_obj).unwrap() {
        let kp = KeyPair::from_py_seed(&hex::decode(s(spec, "py_seed")).unwrap());
        let reg = Registry::from_json(regs.get(s(spec, "registry")).unwrap()).unwrap();
        let n2 = now.clone();
        let clock = Box::new(move || n2.load(Ordering::SeqCst) as i128);
        let adopt = spec.get("adopt") == Some(&Json::Bool(true));
        let mut w = Witness::open_with(kp, reg, cid, Store::memory(), Default::default(), clock, adopt).unwrap();
        if spec.get("stamps") == Some(&Json::Bool(true)) {
            w = w.with_stamps(StampKey::from_json(stamp_key.expect("stamp key")).unwrap());
        }
        ws.insert(who.clone(), w);
    }
    let steps = arr(script, "steps");
    for (i, step) in steps.iter().enumerate() {
        now.store(step.get("now").and_then(Json::as_int).unwrap() as i64, Ordering::SeqCst);
        let w = &ws[s(step, "who")];
        let a = arr(step, "args");
        let got = match s(step, "op") {
            "spend" => w.spend(&a[0]).0,
            "release" => w.release(&a[0], &a[1]).0,
            "status" => w.status(&a[0]).0,
            "freeze" => w.freeze(&a[0]).0,
            "adopt" => w.adopt(&a[0], &a[1], a[2].as_arr().unwrap()).0,
            "record" => Ok(a[0].as_str().and_then(|x| w.record(x)).map(|r| r.to_json()).unwrap_or(Json::Null)),
            "sell_stamp" => w.sell_stamp(&a[0]).0,
            "gossip" => w.gossip(&a[0]).0,
            "proofs" => Ok(w.proofs()),
            "charters" => Ok(w.registry().to_json()),
            op => panic!("unknown op {op}"),
        };
        check_outcome(i, step, got);
    }
    steps.len()
}

/// FREEZE (one successor, evidence with own votes), ADOPT (lone binding, CONTESTED siblings,
/// own-vote abstention for a re-used key, malformed evidence skipped), RELEASE of CONTESTED
/// records, and both rotation regressions of tests/test_conformance.py.
#[test]
fn rotation_script_matches_reference() {
    let v = vectors();
    let n = replay_script(v.get("rotation").unwrap(), None);
    assert!(n > 60, "{n} steps");
}

/// Charter chains, forks, equivocation proofs and the per-message caps of `/v0/gossip`.
#[test]
fn gossip_script_matches_reference() {
    let v = vectors();
    replay_script(v.get("gossip").unwrap(), None);
}

/// Blind stamps: full-domain hash, blind signing, verification and redemption on SPEND.
#[test]
fn stamps_match_reference() {
    let v = vectors();
    let st = v.get("stamps").unwrap();
    let key = StampKey::from_json(st.get("key").unwrap()).unwrap();
    let hexn = |x: &Json, k: &str| sigil_witness::stamps::parse_hex(s(x, k)).unwrap();
    for c in arr(st, "fdh") {
        assert_eq!(sigil_witness::stamps::to_hex(&full_domain_hash(&key.n, s(c, "serial"))), s(c, "fdh"));
    }
    for c in arr(st, "blind") {
        let r = hexn(c, "r");
        let blinded = sigil_witness::stamps::blind(&key.n, &key.e, s(c, "serial"), &r);
        assert_eq!(sigil_witness::stamps::to_hex(&blinded), s(c, "blinded"));
        let bsig = key.sign_blinded(&blinded).unwrap();
        assert_eq!(sigil_witness::stamps::to_hex(&bsig), s(c, "blind_sig"));
        let sig = sigil_witness::stamps::unblind(&key.n, &bsig, &r).unwrap();
        assert_eq!(sigil_witness::stamps::to_hex(&sig), s(c, "sig"));
    }
    for c in arr(st, "verify") {
        assert_eq!(key.verify(c.get("stamp").unwrap()), expected(c), "stamp {}", s(c, "name"));
    }
    replay_script(st.get("script").unwrap(), st.get("key"));
}

/// Replay a scripted run of the reference witness: every vote must be byte-identical and every
/// rejection must be of the same kind.
#[test]
fn witness_script_matches_reference() {
    let v = vectors();
    let wv = v.get("witness").unwrap();
    let reg = Registry::from_json(wv.get("registry").unwrap()).unwrap();
    let kp = KeyPair::from_py_seed(&hex::decode(s(wv, "key_py_seed")).unwrap());
    let now = Arc::new(AtomicI64::new(0));
    let n2 = now.clone();
    let w = Witness::open(kp, reg, s(wv, "cid"), Store::memory(), Default::default(), Box::new(move || n2.load(Ordering::SeqCst) as i128))
        .unwrap();
    for (i, step) in arr(wv, "steps").iter().enumerate() {
        now.store(step.get("now").and_then(Json::as_int).unwrap() as i64, Ordering::SeqCst);
        let args = arr(step, "args");
        let (got, _) = match s(step, "op") {
            "spend" => w.spend(&args[0]),
            "release" => w.release(&args[0], &args[1]),
            "status" => w.status(&args[0]),
            op => panic!("unknown op {op}"),
        };
        let want = step.get("expect").unwrap();
        match (got, want.get("error").and_then(Json::as_str)) {
            (Ok(x), None) => assert_eq!(x.canonical_string(), want.get("ok").unwrap().canonical_string(), "step {i}"),
            (Err(Error::Conflict(vote)), Some("conflict")) => {
                assert_eq!(vote.unwrap_or(Json::Null), *want.get("vote").unwrap(), "step {i}")
            }
            (Err(Error::Rejected(m)), Some("rejected")) => assert_eq!(m, s(want, "message"), "step {i}"),
            (Err(Error::BadRequest(_)), Some("bad_request")) => {}
            (got, _) => panic!("step {i} ({}): got {got:?}, want {}", s(step, "op"), want.canonical_string()),
        }
    }
}
