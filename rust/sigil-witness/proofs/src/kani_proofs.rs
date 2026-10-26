//! Kani bounded proofs. Run with `cargo kani` in rust/sigil-witness/proofs (see
//! docs/VERIFY_RUST.md for the per-harness results and bounds).
//!
//! Two kinds of harness:
//!
//! * on the REAL shipped functions (`sigil_witness::...`): quorum arithmetic, votes_of_seal,
//!   lock-evaluation monotonicity, JSON parser panic freedom (bounded inputs);
//! * on the transcription `model_rust` of the witness's record logic: an inductive proof that
//!   every SPEND/RELEASE step is a TLA+ `Spend`/`Release` step or a stutter and preserves an
//!   invariant that implies "one tid per (sigil, gen)". The transcription is tied to the real
//!   code by tests/refinement_bfs.rs and the witness_ops fuzz target.

use sigil_witness::charter::{faults, quorum};
use sigil_witness::json::{Json, Map};

use crate::model_rust::{self, Core, RustRec, SpendOut, CONTESTED, GEN_LIMIT};
use crate::tla::{self, Tid};

// ------------------------------------------------------------------ quorum arithmetic (real)

/// For every n: no panic, q <= n, and for n >= 1 any two quorums intersect in at least f + 1
/// members (the §8 Lemma 1 counting step), with f < n/3.
#[kani::proof]
fn quorum_intersection_all_n() {
    let n: usize = kani::any();
    let f = faults(n);
    let q = quorum(n);
    assert!(q <= n);
    if n >= 1 {
        assert!(q >= 1);
        assert!(3 * (f as u128) < n as u128);
        assert!(2 * (q as u128) >= n as u128 + f as u128 + 1);
        // q - f honest voters in a quorum is more than the f + ... needed by Lemma 2:
        // 2f < q, so a transition with q - f votes against cannot reach q.
        assert!(2 * (f as u128) < q as u128);
    }
}

/// Documents bug 2 (docs/VERIFY_RUST.md): for n = 0 the Rust quorum is 0, where the spec's
/// floor((n-1)/3) gives f = -1 and q = 1 (and Python's `(n - 1) // 3` agrees with the spec).
#[kani::proof]
fn quorum_of_empty_charter_is_zero() {
    assert_eq!(quorum(0), 0);
}

// ------------------------------------------------------- witness record logic (transcription)
//
// Records are symbolic in every field: generations are unbounded i128 in [0, 2^62], tids any
// of 6 values or CONTESTED, booleans free. The record logic (`model_rust::spend_core` /
// `release_core`) never reads `rec.votes`, it only appends to it, so the vote history is kept
// here as a fixed array of H symbolic votes, each present or not (so every history of 0..=H
// votes is covered). Symbolic-length `Vec`s made CBMC run out of memory (10 GB). The
// invariant's clauses are per vote and per pair of votes and one step appends at most one vote,
// so a violation in a longer history would already show with the (at most two) votes involved;
// that generalisation is an informal argument, the proofs are for H = 2.

const H: usize = 2;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Hist {
    v: [(i128, Tid); H + 1],
    present: [bool; H + 1],
}

impl Hist {
    const EMPTY: Hist = Hist { v: [(0, 0); H + 1], present: [false; H + 1] };

    fn any() -> Hist {
        let mut h = Hist::EMPTY;
        for i in 0..H {
            h.v[i] = (any_gen(), kani::any());
            kani::assume(h.v[i].1 < 6);
            h.present[i] = kani::any();
        }
        h
    }
    fn contains(&self, x: (i128, Tid)) -> bool {
        (0..=H).any(|i| self.present[i] && self.v[i] == x)
    }
    fn push(&mut self, x: (i128, Tid)) {
        self.v[H] = x;
        self.present[H] = true;
    }
}

fn any_tid() -> Tid {
    let t: Tid = kani::any();
    kani::assume(t < 6 || t == CONTESTED);
    t
}

fn any_gen() -> i128 {
    let g: i128 = kani::any();
    kani::assume(g >= 0 && g <= GEN_LIMIT);
    g
}

fn any_core() -> Core {
    let tid = if kani::any() { Some(any_tid()) } else { None };
    let vote = if kani::any() { Some((any_gen(), any_tid())) } else { None };
    Core { gen: any_gen(), tid, vote, abstain: kani::any() }
}

fn no_equivocation(h: &Hist) -> bool {
    (0..=H).all(|i| (0..=H).all(|j| !(h.present[i] && h.present[j] && h.v[i].0 == h.v[j].0 && h.v[i].1 != h.v[j].1)))
}

/// The inductive invariant of one record: generation in range; the stored vote (if any) is for
/// the bound tid at the current generation and is in the history; every vote in the history is
/// at or below the current generation, and one at the current generation is either the stored
/// vote or the reason for `abstain`; and the history has one tid per generation.
fn inv(r: &Core, h: &Hist) -> bool {
    // A bound record's generation passed `authorises` (< 2^62); a release adds one.
    let gen_ok = r.gen >= 0 && r.gen <= GEN_LIMIT && (r.tid.is_none() || r.tid == Some(CONTESTED) || r.gen < GEN_LIMIT);
    let vote_ok = match r.vote {
        Some((g, t)) => r.tid == Some(t) && t != CONTESTED && g == r.gen && h.contains((g, t)),
        None => true,
    };
    let hist_ok = (0..=H).all(|i| {
        let (g, t) = h.v[i];
        !h.present[i]
            || (g >= 0
                && g <= r.gen
                && (g < r.gen || (r.tid == Some(t) && r.vote == Some((g, t))) || (r.abstain && r.vote.is_none())))
    });
    gen_ok && vote_ok && hist_ok && no_equivocation(h)
}

fn alpha(c: &Core) -> tla::AbsRec {
    tla::AbsRec { gen: c.gen, bound: c.tid }
}

#[kani::proof]
fn init_satisfies_invariant() {
    assert!(inv(&Core::default(), &Hist::EMPTY));
    assert_eq!(RustRec::default().alpha(), tla::AbsRec::INIT);
    assert_eq!(alpha(&Core::default()), tla::AbsRec::INIT);
}

/// SPEND: from any record satisfying `inv` (or no record), with any authorisation outcome,
/// expiry, header generation (0 <= g < 2^62, what `authorises` admits) and tid, the step is
/// either a stutter that changes nothing, or exactly TLA+ `Spend(w, s, t)` with
/// `votes' = votes ∪ {(g, t)}`; and `inv` (hence one tid per generation) still holds.
#[kani::proof]
#[kani::unwind(5)]
fn spend_refines_tla_and_preserves_invariant() {
    let exists: bool = kani::any();
    let pre = if exists { any_core() } else { Core::default() };
    let hist = if exists { Hist::any() } else { Hist::EMPTY };
    kani::assume(inv(&pre, &hist));
    let authorised: bool = kani::any();
    let expired: bool = kani::any();
    let g: i128 = kani::any();
    kani::assume(g >= 0 && g < GEN_LIMIT);
    let t: Tid = kani::any();
    kani::assume(t < 6); // a real tid is a 64-hex hash, never "!contested"
    let (out, post, pushed) = model_rust::spend_core(if exists { Some(pre) } else { None }, authorised, expired, g, t);
    let post_core = post.unwrap_or_default();
    let mut post_hist = hist;
    if let Some(x) = pushed {
        post_hist.push(x);
    }
    match out {
        SpendOut::Vote(v) => {
            assert!(authorised);
            assert_eq!(v, (g, t));
            assert_eq!(tla::spend(alpha(&pre), g, t), Some(alpha(&post_core)));
            // votes' = votes ∪ {(g, t)}: already there, or exactly that vote appended.
            assert!(pushed.is_none() || pushed == Some((g, t)));
            assert!(hist.contains((g, t)) || pushed == Some((g, t)));
        }
        SpendOut::Conflict(v) => {
            assert_eq!(v, pre.vote);
            assert_eq!(post_core, pre);
            assert!(pushed.is_none());
            // A conflict only ever carries our vote for another tid at this very generation.
            if let Some((vg, vt)) = v {
                assert!(vg == g && vt != t);
            }
        }
        SpendOut::Rejected => {
            assert_eq!(post_core, pre);
            assert!(pushed.is_none());
        }
    }
    assert!(inv(&post_core, &post_hist));
}

/// RELEASE: only from a bound, non-contested record and only with a valid proof; exactly TLA+
/// `Release(w, s)`; votes unchanged; `gen + 1` cannot overflow; `inv` preserved.
#[kani::proof]
#[kani::unwind(5)]
fn release_refines_tla_and_preserves_invariant() {
    let exists: bool = kani::any();
    let pre = if exists { any_core() } else { Core::default() };
    let hist = if exists { Hist::any() } else { Hist::EMPTY };
    kani::assume(inv(&pre, &hist));
    let frozen: bool = kani::any();
    let proof_ok: bool = kani::any();
    let (out, post) = model_rust::release_core(if exists { Some(pre) } else { None }, frozen, proof_ok);
    let post_core = post.unwrap_or_default();
    match out {
        Ok(g) => {
            assert!(proof_ok && !frozen && exists);
            assert!(pre.tid.is_some() && pre.tid != Some(CONTESTED));
            assert_eq!(tla::release(alpha(&pre), proof_ok), Some(alpha(&post_core)));
            assert_eq!(g, post_core.gen);
        }
        Err(()) => assert_eq!(post_core, pre),
    }
    assert!(inv(&post_core, &hist));
}

// ------------------------------------------------------------------- votes_of_seal (real)

fn small_json() -> Json {
    match kani::any::<u8>() % 4 {
        0 => Json::Null,
        1 => Json::Int(kani::any::<i8>() as i128),
        2 => Json::Str(if kani::any() { "x".into() } else { "y".into() }),
        _ => Json::Bool(kani::any()),
    }
}

/// `proofs::votes_of_seal` never lets an entry override the seal's
/// constellation/version/sigil/gen/tid, keeps every entry's witness/time/sig, and refuses any
/// entry that is not exactly `{witness, time, sig}` (bounded: up to 2 entries, entry keys drawn
/// from the 5 seal fields plus the 3 vote fields).
#[kani::proof]
#[kani::unwind(10)]
fn votes_of_seal_never_overrides() {
    const COMMON: [&str; 5] = ["constellation", "version", "sigil", "gen", "tid"];
    const OWN: [&str; 3] = ["witness", "time", "sig"];
    let mut seal = Map::new();
    for k in COMMON {
        if kani::any() {
            seal.insert(k.to_string(), small_json());
        }
    }
    let n: usize = kani::any();
    kani::assume(n <= 2);
    let mut entries = Vec::new();
    for _ in 0..n {
        let mut e = Map::new();
        for k in OWN.iter().chain(COMMON.iter()) {
            if kani::any() {
                e.insert(k.to_string(), small_json());
            }
        }
        entries.push(Json::Obj(e));
    }
    seal.insert("votes".into(), Json::Arr(entries.clone()));
    let seal = Json::Obj(seal);
    let got = sigil_witness::proofs::votes_of_seal(&seal);
    if let Some(vs) = got {
        assert_eq!(vs.len(), entries.len());
        for (v, e) in vs.iter().zip(&entries) {
            for k in COMMON {
                assert!(seal.get(k).is_some());
                assert_eq!(v.get(k), seal.get(k));
            }
            for k in OWN {
                assert_eq!(v.get(k), e.get(k));
            }
            assert_eq!(e.as_obj().map(|m| m.len()), Some(3));
        }
    }
}

// ----------------------------------------------------- lock evaluation monotonicity (real)

fn time_leaf() -> Json {
    let mut m = Map::new();
    match kani::any::<u8>() % 4 {
        0 => {
            m.insert("op".into(), Json::str("after"));
            m.insert("t".into(), Json::Int(kani::any::<i64>() as i128));
        }
        1 => {
            m.insert("op".into(), Json::str("before"));
            m.insert("t".into(), Json::Int(kani::any::<i64>() as i128));
        }
        2 => {
            m.insert("op".into(), Json::str("never"));
        }
        _ => {
            // A signature that is absent from the unlock: false, no cryptography reached.
            m.insert("op".into(), Json::str("sig"));
            m.insert("pk".into(), Json::str("p"));
        }
    }
    Json::Obj(m)
}

fn combinator(children: Vec<Json>) -> Json {
    let mut m = Map::new();
    m.insert("op".into(), Json::str(if kani::any() { "all" } else { "any" }));
    m.insert("of".into(), Json::Arr(children));
    Json::Obj(m)
}

/// The claim `Witness::spend` relies on to evaluate a lock once ("the lock language is
/// monotone"): for the REAL `locks::evaluate`, a lock that holds at some clock also holds with
/// time conditions ignored. Bounded: locks of depth <= 2 with <= 2 children per combinator over
/// after/before/never/sig leaves, any i64 times and clock.
#[kani::proof]
#[kani::unwind(8)]
fn lock_eval_monotone_in_time() {
    let lock = if kani::any() {
        time_leaf()
    } else {
        let a = if kani::any() { time_leaf() } else { combinator(vec![time_leaf(), time_leaf()]) };
        let b = time_leaf();
        if kani::any() {
            combinator(vec![a])
        } else {
            combinator(vec![a, b])
        }
    };
    let mut u = Map::new();
    u.insert("expires".into(), Json::Int(0));
    let unlock = Json::Obj(u);
    let now = kani::any::<i64>() as i128;
    let at_now = sigil_witness::locks::evaluate(&lock, &unlock, "s", "t", Some(now), false);
    let untimed = sigil_witness::locks::evaluate(&lock, &unlock, "s", "t", None, false);
    assert!(!at_now || untimed);
}

// ------------------------------------------------------------ JSON parser panic freedom (real)

/// `json::parse` never panics on any input of up to N bytes that contains no '.', 'e' or 'E'
/// (so no float is parsed: float parsing and printing are out of Kani's reach and are covered
/// by fuzzing and the Python differential instead).
fn parse_no_panic<const N: usize>() {
    let bytes: [u8; N] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= N);
    for b in &bytes[..len] {
        kani::assume(*b != b'.' && *b != b'e' && *b != b'E');
    }
    let _ = sigil_witness::json::parse(&bytes[..len]);
}

#[kani::proof]
#[kani::unwind(9)]
fn parse_no_panic_7() {
    parse_no_panic::<7>();
}

/// Expected to FAIL (bug 1): 8 bytes suffice to make `Parser::hex4` slice a `str` inside a
/// multi-byte character, e.g. `"\u111` followed by `é`.
#[kani::proof]
#[kani::unwind(10)]
fn parse_no_panic_8_finds_bug_1() {
    parse_no_panic::<8>();
}
