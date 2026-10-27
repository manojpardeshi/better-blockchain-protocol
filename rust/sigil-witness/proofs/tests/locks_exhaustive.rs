//! Exhaustive bounded check of the REAL `locks::evaluate` (no Kani needed): every lock of
//! depth <= 2 with 1 or 2 children per `all`/`any`, over 9 leaves (`after t` and `before t`
//! for t in {-1, 0, 1}, `never`, a `sig` whose signature is absent, a `sig` with a real valid
//! signature), at every clock in {-2, ..., 2} and with time ignored.
//!
//! Checks, for each of the 72,000 or so locks:
//! * monotonicity in time, which `Witness::spend` relies on to evaluate a lock once:
//!   eval(now) implies eval(None);
//! * agreement with an independent evaluator of SPEC §3.5's boolean semantics;
//! * batch and single signature verification agree.

use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{obj, Json, Map};
use sigil_witness::locks::evaluate;
use sigil_witness::model::unlock_message;

#[derive(Clone)]
enum L {
    After(i128),
    Before(i128),
    Never,
    SigAbsent,
    SigPresent,
    All(Vec<L>),
    Any(Vec<L>),
}

fn json(l: &L, absent: &str, present: &str) -> Json {
    match l {
        L::After(t) => obj([("op", "after".into()), ("t", Json::Int(*t))]),
        L::Before(t) => obj([("op", "before".into()), ("t", Json::Int(*t))]),
        L::Never => obj([("op", "never".into())]),
        L::SigAbsent => obj([("op", "sig".into()), ("pk", Json::str(absent))]),
        L::SigPresent => obj([("op", "sig".into()), ("pk", Json::str(present))]),
        L::All(of) => obj([("op", "all".into()), ("of", Json::Arr(of.iter().map(|x| json(x, absent, present)).collect()))]),
        L::Any(of) => obj([("op", "any".into()), ("of", Json::Arr(of.iter().map(|x| json(x, absent, present)).collect()))]),
    }
}

fn spec_eval(l: &L, now: Option<i128>) -> bool {
    match l {
        L::After(t) => now.map_or(true, |n| n >= *t),
        L::Before(t) => now.map_or(true, |n| n < *t),
        L::Never | L::SigAbsent => false,
        L::SigPresent => true,
        L::All(of) => of.iter().all(|x| spec_eval(x, now)),
        L::Any(of) => of.iter().any(|x| spec_eval(x, now)),
    }
}

#[test]
fn lock_evaluation_is_monotone_in_time_and_matches_the_spec() {
    let present = KeyPair::from_seed(&[1; 32]);
    let absent = KeyPair::from_seed(&[2; 32]);
    let (sigil, tid) = ("s".repeat(64), "t".repeat(64));
    let sig = present.sign("unlock", &unlock_message(&sigil, &tid, Json::Int(0)));
    let mut sigs = Map::new();
    sigs.insert(present.pk.clone(), Json::Str(sig));
    let unlock = obj([("sigs", Json::Obj(sigs)), ("expires", Json::Int(0))]);

    let mut leaves = vec![L::Never, L::SigAbsent, L::SigPresent];
    for t in -1..=1 {
        leaves.push(L::After(t));
        leaves.push(L::Before(t));
    }
    let combine = |items: &[L]| -> Vec<L> {
        let mut out = Vec::new();
        for a in items {
            out.push(L::All(vec![a.clone()]));
            out.push(L::Any(vec![a.clone()]));
            for b in items {
                out.push(L::All(vec![a.clone(), b.clone()]));
                out.push(L::Any(vec![a.clone(), b.clone()]));
            }
        }
        out
    };
    let depth1 = combine(&leaves);
    let mut level1 = leaves.clone();
    level1.extend(depth1.iter().cloned());
    let mut locks = level1.clone();
    locks.extend(combine(&level1));

    let mut checked = 0u64;
    for l in &locks {
        let j = json(l, &absent.pk, &present.pk);
        let untimed = evaluate(&j, &unlock, &sigil, &tid, None, false);
        assert_eq!(untimed, spec_eval(l, None), "{}", j.canonical_string());
        for now in -2..=2 {
            let at = evaluate(&j, &unlock, &sigil, &tid, Some(now), false);
            assert_eq!(at, spec_eval(l, Some(now)), "{} at {now}", j.canonical_string());
            assert!(!at || untimed, "not monotone: {} at {now}", j.canonical_string());
            checked += 1;
        }
        assert_eq!(untimed, evaluate(&j, &unlock, &sigil, &tid, None, true));
    }
    eprintln!("RESULT: {} locks, {} timed evaluations, all monotone and as specified", locks.len(), checked);
}
