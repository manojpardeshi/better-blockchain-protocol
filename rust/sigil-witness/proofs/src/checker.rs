//! Drive a real `Witness` and check every step against
//!
//! 1. the TLA+ `Next` for one witness (`tla::spend` / `tla::release` / stuttering), through the
//!    abstraction function α computed from STATUS;
//! 2. the transcription `model_rust` (so the Kani proofs about it apply to this run);
//! 3. the invariants: one tid per `(sigil, gen)` over every vote `w0` ever lets out, every vote
//!    is `w0`'s, for the request's sigil, homed at `w0`'s constellation, correctly signed, and
//!    stored (in STATUS) before the reply; RELEASE only on a death proof that the spec-level
//!    oracle accepts (soundness), and on every proof it accepts (completeness, a liveness and
//!    compatibility check).
//!
//! A violation panics with a message starting `SAFETY:`, `REFINEMENT:`, `MODEL:` or `LIVENESS:`.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

use sigil_witness::charter::Registry;
use sigil_witness::json::Json;
use sigil_witness::model::transition_id;
use sigil_witness::proofs::verify_vote;
use sigil_witness::store::{Loaded, Store};
use sigil_witness::witness::{Error, Record, Witness};

use crate::model_rust::{self, RustRec, SpendOut};
use crate::tla::{self, AbsRec};
use crate::world::{Genuine, ProofSpec, World, C, NOW};

/// `SIGIL_NO_MODEL=1` turns the transcription (`MODEL:`) checks off, so that mutation testing
/// can show which bugs the TLA+ refinement and safety checks catch on their own.
pub fn model_checks() -> bool {
    std::env::var_os("SIGIL_NO_MODEL").is_none()
}

#[macro_export]
macro_rules! model_eq {
    ($($t:tt)*) => {
        if $crate::checker::model_checks() {
            assert_eq!($($t)*);
        }
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    /// `later`: the clock reads NOW + 1 (a re-request must get the STORED vote, not a new one).
    Spend { si: usize, hi: usize, lock_ok: bool, expired: bool, later: bool },
    Release { si: usize, spec: ProofSpec },
    Status { si: usize },
}

/// STATUS of one sigil, as α sees it.
#[derive(Clone, Debug, PartialEq)]
pub struct Obs {
    pub gen: i128,
    pub tid: Option<String>,
    pub votes: Vec<Json>,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub steps: u64,
    pub votes: u64,
    pub conflicts: u64,
    pub rejects: u64,
    pub releases: u64,
    pub release_rejects: u64,
}

pub struct Checker<'w> {
    pub world: &'w World,
    pub w: Witness,
    pub clock: Arc<AtomicI64>,
    /// Transcription state per known sigil.
    pub shadow: BTreeMap<String, RustRec>,
    pub genuine: Genuine,
    /// `(sigil, gen) -> tid` over every vote w0 ever let out.
    pub cast: HashMap<(String, i128), String>,
    pub extra_tids: HashMap<String, u32>,
    pub stats: Stats,
    /// Check that every proof the oracle accepts is accepted (off for raw fuzzed proofs).
    pub check_completeness: bool,
}

pub fn open_witness(world: &World, store: Arc<Store>, loaded: Loaded, clock: Arc<AtomicI64>) -> Witness {
    let reg = Registry::from_json(&world.registry).expect("registry");
    let c2 = clock.clone();
    Witness::open(world.w0_key(), reg, world.cid(C), store, loaded, Box::new(move || c2.load(Ordering::SeqCst) as i128))
        .expect("open witness")
}

impl<'w> Checker<'w> {
    pub fn new(world: &'w World) -> Checker<'w> {
        let clock = Arc::new(AtomicI64::new(NOW as i64));
        let w = open_witness(world, Store::memory(), Loaded::default(), clock.clone());
        Checker::with_witness(world, w, clock, BTreeMap::new())
    }

    pub fn with_witness(world: &'w World, w: Witness, clock: Arc<AtomicI64>, shadow: BTreeMap<String, RustRec>) -> Checker<'w> {
        let mut c = Checker {
            world,
            w,
            clock,
            shadow,
            genuine: Genuine::default(),
            cast: HashMap::new(),
            extra_tids: HashMap::new(),
            stats: Stats::default(),
            check_completeness: true,
        };
        // Votes already in a restored store are w0's own, hence genuine.
        for si in 0..world.sigils.len() {
            let o = c.obs_of(&world.sigils[si].sigil.clone());
            for v in &o.votes {
                c.genuine.add(v);
                c.note_cast(v);
            }
        }
        c
    }

    pub fn obs_of(&self, sigil: &str) -> Obs {
        let (r, _) = self.w.status(&Json::str(sigil));
        let r = r.expect("STATUS of a string never fails");
        Obs {
            gen: r.get("gen").and_then(Json::as_int).expect("gen"),
            tid: r.get("tid").and_then(Json::as_str).map(str::to_string),
            votes: r.get("votes").and_then(Json::as_arr).cloned().expect("votes"),
        }
    }

    fn all_obs(&self) -> Vec<(String, Obs)> {
        let mut keys: Vec<String> = self.world.sigils.iter().map(|s| s.sigil.clone()).collect();
        for k in self.shadow.keys() {
            if !keys.contains(k) {
                keys.push(k.clone());
            }
        }
        keys.into_iter().map(|s| {
            let o = self.obs_of(&s);
            (s, o)
        }).collect()
    }

    fn tid_ix(&mut self, t: &str) -> u32 {
        self.world.tid_index(t, &mut self.extra_tids)
    }

    fn alpha(&mut self, o: &Obs) -> AbsRec {
        let bound = o.tid.clone().map(|t| self.tid_ix(&t));
        AbsRec { gen: o.gen, bound }
    }

    fn vote_pairs(&mut self, o: &Obs) -> Vec<(i128, u32)> {
        o.votes
            .iter()
            .map(|v| {
                let g = v.get("gen").and_then(Json::as_int).expect("vote gen");
                let t = v.get("tid").and_then(Json::as_str).expect("vote tid").to_string();
                (g, self.tid_ix(&t))
            })
            .collect()
    }

    /// Check a vote that left w0: well formed, w0's, for `sigil`, homed here, signed, and
    /// consistent with every other vote w0 ever cast.
    fn check_vote(&mut self, v: &Json, sigil: &str) {
        let w = self.world;
        assert!(verify_vote(v), "SAFETY: w0 let out a vote with an invalid signature: {}", v.canonical_string());
        assert_eq!(v.get("witness").and_then(Json::as_str), Some(self.w.pk.as_str()), "SAFETY: vote not by w0");
        assert_eq!(v.get("constellation").and_then(Json::as_str), Some(w.cid(C)), "SAFETY: vote for a foreign constellation");
        assert_eq!(v.get("version"), Some(&Json::Int(0)), "SAFETY: vote version");
        assert_eq!(v.get("sigil").and_then(Json::as_str), Some(sigil), "SAFETY: vote for another sigil");
        if let Some(si) = w.sigil_index(sigil) {
            assert_eq!(w.sigils[si].home, C, "SAFETY: w0 voted on a sigil homed elsewhere (Home[s] = ConsOf(w) violated)");
        }
        self.genuine.add(v);
        self.note_cast(v);
    }

    fn note_cast(&mut self, v: &Json) {
        let s = v.get("sigil").and_then(Json::as_str).unwrap_or("").to_string();
        let g = v.get("gen").and_then(Json::as_int).unwrap_or(-1);
        let t = v.get("tid").and_then(Json::as_str).unwrap_or("").to_string();
        if let Some(prev) = self.cast.get(&(s.clone(), g)) {
            assert_eq!(prev, &t, "SAFETY: w0 voted two tids at one (sigil, gen) = ({s}, {g})");
        } else {
            self.cast.insert((s, g), t);
        }
    }

    fn check_frame(&self, before: &[(String, Obs)], after: &[(String, Obs)], touched: &str) {
        for ((s, a), (s2, b)) in before.iter().zip(after) {
            assert_eq!(s, s2);
            if s != touched {
                assert_eq!(a, b, "REFINEMENT: a step on {touched} changed sigil {s}");
            }
        }
    }

    fn check_status_matches_shadow(&mut self, sigil: &str, o: &Obs) {
        let sh = self.shadow.get(sigil).cloned().unwrap_or_default();
        let a = self.alpha(o);
        crate::model_eq!(a, sh.alpha(), "MODEL: STATUS of {sigil} differs from the transcription");
        let pairs = self.vote_pairs(o);
        crate::model_eq!(pairs, sh.votes, "MODEL: STATUS votes of {sigil} differ from the transcription");
        for v in &o.votes {
            self.check_vote(v, sigil);
        }
    }

    pub fn step(&mut self, op: &Op) {
        self.stats.steps += 1;
        self.clock.store(NOW as i64, Ordering::SeqCst);
        match *op {
            Op::Spend { si, hi, lock_ok, expired, later } => {
                self.clock.store(NOW as i64 + later as i64, Ordering::SeqCst);
                self.spend(si, hi, lock_ok, expired)
            }
            Op::Release { si, spec } => self.release(si, &spec),
            Op::Status { si } => {
                let s = self.world.sigils[si].sigil.clone();
                let o = self.obs_of(&s);
                self.check_status_matches_shadow(&s, &o);
            }
        }
    }

    fn spend(&mut self, si: usize, hi: usize, lock_ok: bool, expired: bool) {
        let world = self.world;
        let sigil = world.sigils[si].sigil.clone();
        let req = world.spend_request(si, hi, lock_ok, expired);
        let auth = world.authorised(si, hi, lock_ok);
        let g = world.gen_in(si, hi).unwrap_or(-1);
        let t = hi as u32;
        self.do_spend(&sigil, &req, Some((auth, expired, g, t)));
    }

    /// Run SPEND. `known` = (authorised, expired, gen, tid) when the harness built the request;
    /// `None` for a raw (fuzzed) request, where only what the reply implies can be checked.
    pub fn do_spend(&mut self, sigil: &str, req: &Json, known: Option<(bool, bool, i128, u32)>) {
        let before = self.all_obs();
        let pre = self.obs_of(sigil);
        let pre_abs = self.alpha(&pre);
        let (res, _) = self.w.spend(req);
        let after = self.all_obs();
        self.check_frame(&before, &after, sigil);
        let post = self.obs_of(sigil);
        let post_abs = self.alpha(&post);
        let actual = match &res {
            Ok(v) => {
                self.stats.votes += 1;
                self.check_vote(v, sigil);
                assert!(post.votes.contains(v), "SAFETY: vote let out but not stored");
                let vg = v.get("gen").and_then(Json::as_int).expect("gen");
                let vt = v.get("tid").and_then(Json::as_str).expect("tid").to_string();
                // The vote's tid is the hash of the request's header, which names [sigil, gen] once.
                let header = req.get("header").cloned().unwrap_or(Json::Null);
                assert_eq!(transition_id(&header), vt, "SAFETY: vote tid is not the request header's tid");
                let n = header
                    .get("inputs")
                    .and_then(Json::as_arr)
                    .map(|a| a.iter().filter(|x| x.as_arr().is_some_and(|p| p.len() == 2 && p[0].as_str() == Some(sigil))).count())
                    .unwrap_or(0);
                assert_eq!(n, 1, "SAFETY: voted on a header that does not name the sigil exactly once");
                SpendOut::Vote((vg, self.tid_ix(&vt)))
            }
            Err(Error::Conflict(v)) => {
                self.stats.conflicts += 1;
                let p = v.as_ref().map(|v| {
                    self.check_vote(v, sigil);
                    assert!(post.votes.contains(v), "SAFETY: conflict carries a vote that is not stored");
                    let vg = v.get("gen").and_then(Json::as_int).expect("gen");
                    let vt = v.get("tid").and_then(Json::as_str).expect("tid").to_string();
                    (vg, self.tid_ix(&vt))
                });
                SpendOut::Conflict(p)
            }
            Err(_) => {
                self.stats.rejects += 1;
                SpendOut::Rejected
            }
        };
        // Refinement: a SPEND either stutters or is TLA+ Spend(w0, s, t) with g = GenOf(t, s).
        let pre_pairs = self.vote_pairs(&pre);
        let post_pairs = self.vote_pairs(&post);
        let changed = pre_abs != post_abs || pre_pairs != post_pairs;
        if let SpendOut::Vote((vg, vt)) = actual {
            let next = tla::spend(pre_abs, vg, vt);
            assert_eq!(next, Some(post_abs), "REFINEMENT: vote not allowed by TLA+ Spend from {pre_abs:?} (g={vg}, t={vt})");
            let mut want = pre_pairs.clone();
            if !want.contains(&(vg, vt)) {
                want.push((vg, vt));
            }
            assert_eq!(post_pairs, want, "REFINEMENT: votes' != votes ∪ {{<<c,w,s,g,t>>}}");
        } else {
            assert!(!changed, "REFINEMENT: a SPEND that did not vote changed state: {pre:?} -> {post:?}");
        }
        // Transcription.
        let existing = self.shadow.get(sigil).cloned();
        match known {
            Some((auth, expired, g, t)) => {
                let (want, rec) = model_rust::spend(existing.as_ref(), auth, expired, g, t);
                crate::model_eq!(actual, want, "MODEL: spend reply differs from the transcription");
                self.set_shadow(sigil, rec);
            }
            None => {
                if actual != SpendOut::Rejected {
                    let (vg, vt) = match &actual {
                        SpendOut::Vote(p) => *p,
                        _ => {
                            // A conflict: the request's (gen, tid) are unknown to us; the state
                            // did not change (checked above).
                            self.check_status_matches_shadow(sigil, &post);
                            return;
                        }
                    };
                    let (want, rec) = model_rust::spend(existing.as_ref(), true, false, vg, vt);
                    crate::model_eq!(actual, want, "MODEL: raw spend reply differs from the transcription");
                    self.set_shadow(sigil, rec);
                }
            }
        }
        // A raw request may name a sigil the harness has not seen: it is tracked from now on.
        self.check_status_matches_shadow(sigil, &post);
    }

    fn set_shadow(&mut self, sigil: &str, rec: Option<RustRec>) {
        match rec {
            Some(r) => {
                self.shadow.insert(sigil.to_string(), r);
            }
            None => {
                self.shadow.remove(sigil);
            }
        }
    }

    fn release(&mut self, si: usize, spec: &ProofSpec) {
        let (sigil, proof) = self.build_release_proof(si, spec);
        self.do_release(&sigil, &proof);
    }

    /// The death proof `spec` describes, against the header bound at `si` (or header 0).
    pub fn build_release_proof(&mut self, si: usize, spec: &ProofSpec) -> (String, Json) {
        let world = self.world;
        let sigil = world.sigils[si].sigil.clone();
        let pre = self.obs_of(&sigil);
        let ht = pre.tid.as_deref().and_then(|t| world.headers.iter().position(|h| h.tid == t)).unwrap_or(0);
        let w0 = &self.w;
        let w0_votes = |s: usize| -> Vec<Json> {
            let (r, _) = w0.status(&Json::str(&world.sigils[s].sigil));
            r.ok().and_then(|r| r.get("votes").and_then(Json::as_arr).cloned()).unwrap_or_default()
        };
        let mut genuine = std::mem::take(&mut self.genuine);
        let proof = world.build_proof(spec, ht, &w0_votes, &mut genuine);
        self.genuine = genuine;
        (sigil, proof)
    }

    /// RELEASE with an arbitrary sigil value: must not panic; a non-string changes nothing.
    pub fn do_release_raw(&mut self, sigil: &Json, proof: &Json) {
        if let Some(s) = sigil.as_str() {
            let s = s.to_string();
            let keep = self.check_completeness;
            self.check_completeness = false;
            self.do_release(&s, proof);
            self.check_completeness = keep;
            return;
        }
        let before = self.all_obs();
        let (r, _) = self.w.release(sigil, proof);
        assert!(r.is_err(), "RELEASE of a non-string sigil succeeded");
        assert_eq!(before, self.all_obs(), "REFINEMENT: RELEASE of a non-string sigil changed state");
    }

    /// Run RELEASE with any proof and check it.
    pub fn do_release(&mut self, sigil: &str, proof: &Json) {
        let before = self.all_obs();
        let pre = self.obs_of(sigil);
        let pre_abs = self.alpha(&pre);
        let (oracle, strict) = match &pre.tid {
            Some(t) => {
                let header = self.world.headers.iter().find(|h| &h.tid == t).map(|h| h.header.clone());
                match header {
                    Some(h) => self.world.oracle_dead(&h, t, proof, &self.genuine),
                    None => (false, false),
                }
            }
            None => (false, false),
        };
        let (res, _) = self.w.release(&Json::str(sigil), proof);
        let after = self.all_obs();
        self.check_frame(&before, &after, sigil);
        let post = self.obs_of(sigil);
        let post_abs = self.alpha(&post);
        let ok = match res {
            Ok(g) => {
                self.stats.releases += 1;
                assert!(oracle, "SAFETY: RELEASE accepted a death proof the spec oracle rejects: {}", proof.canonical_string());
                assert_eq!(Json::Int(post.gen), g, "RELEASE reply is not the new generation");
                let next = tla::release(pre_abs, oracle);
                assert_eq!(next, Some(post_abs), "REFINEMENT: release not allowed by TLA+ Release from {pre_abs:?}");
                assert_eq!(pre.votes, post.votes, "REFINEMENT: RELEASE changed votes");
                true
            }
            Err(_) => {
                self.stats.release_rejects += 1;
                assert_eq!(pre, post, "REFINEMENT: a rejected RELEASE changed state");
                if self.check_completeness && strict && pre_abs.bound.is_some() {
                    panic!("LIVENESS: RELEASE rejected a death proof the spec oracle accepts: {}", proof.canonical_string());
                }
                false
            }
        };
        let existing = self.shadow.get(sigil).cloned();
        let (want, rec) = model_rust::release(existing.as_ref(), false, ok);
        crate::model_eq!(want.is_ok(), ok, "MODEL: release outcome differs from the transcription");
        self.set_shadow(sigil, rec);
        self.check_status_matches_shadow(sigil, &post);
    }

    /// Raw STATUS on any JSON value: must never panic and never change state.
    pub fn do_status_raw(&mut self, sigil: &Json) {
        let before = self.all_obs();
        let (r, _) = self.w.status(sigil);
        if let (Ok(r), Some(s)) = (&r, sigil.as_str()) {
            if let Some(vs) = r.get("votes").and_then(Json::as_arr) {
                for v in vs.clone() {
                    self.check_vote(&v, s);
                }
            }
        }
        let after = self.all_obs();
        assert_eq!(before, after, "REFINEMENT: STATUS changed state");
    }
}

/// The record of a sigil as a store holds it, with its (write-only) log dropped.
pub fn strip_log(r: &Json) -> Json {
    let mut rec = Record::from_json(r).expect("record");
    rec.log.clear();
    rec.to_json()
}
