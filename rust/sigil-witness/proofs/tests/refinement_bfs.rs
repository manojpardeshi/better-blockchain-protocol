//! Bounded exhaustive refinement check of the REAL witness against formal/Sigil.tla.
//!
//! Breadth-first search over every state of `w0` reachable with the op alphabet below, to a
//! fixpoint (the alphabet's generations are bounded, so the reachable state space is finite).
//! Every transition runs the real `Witness::spend` / `release` / `status`, restored from the
//! parent state's full record table and with a real redb store, and is checked by
//! `Checker::step` (TLA+ refinement through α, the transcription, safety invariants). After
//! the step the store is reopened and the persisted records are compared field by field with
//! the transcription (`gen`, `tid`, `vote`, `abstain`, `votes`), so hidden state is checked too.
//!
//! State identity is the record table with the `log` field dropped: `log` is write-only in
//! witness.rs (`grep -n "\.log" src/witness.rs` shows only `push`), so it cannot influence any
//! reply; `tests/restart_equivalence` in this crate checks that dropping it on restore changes
//! no reply.
//!
//! `SIGIL_BFS_FULL=1` uses the full alphabet (all proof shapes); the default is a reduced one.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use std::sync::Arc;

use sigil_witness::json::Json;
use sigil_witness::store::{Loaded, Store};
use sigil_witness::witness::Record;
use sigil_witness_proofs::checker::{open_witness, strip_log, Checker, Op};
use sigil_witness_proofs::model_rust::{RustRec, CONTESTED};
use sigil_witness_proofs::world::{default_headers, ProofSpec, Src, UChoice, World, NOW};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Key(String);

#[derive(Clone)]
struct State {
    records: BTreeMap<String, Json>,
    shadow: BTreeMap<String, RustRec>,
}

impl State {
    fn key(&self) -> Key {
        let r: Vec<String> = self.records.iter().map(|(k, v)| format!("{k}={}", v.canonical_string())).collect();
        Key(format!("{}#{:?}", r.join(";"), self.shadow))
    }
}

fn alphabet(world: &World, full: bool) -> Vec<Op> {
    let mut ops = Vec::new();
    for si in 0..world.sigils.len() {
        for hi in 0..world.headers.len() {
            for lock_ok in [true, false] {
                for expired in [false, true] {
                    if !full && !lock_ok && expired {
                        continue;
                    }
                    ops.push(Op::Spend { si, hi, lock_ok, expired, later: false });
                    if lock_ok && !expired {
                        ops.push(Op::Spend { si, hi, lock_ok, expired, later: true });
                    }
                }
            }
        }
        ops.push(Op::Status { si });
    }
    let mut specs = Vec::new();
    for k in 0..2 {
        for seal in [true, false] {
            let base = ProofSpec { k, seal, src: Src::Home, u: UChoice::Phantom, full: true, with_w0: false, wrong_parcel: false };
            specs.push(base);
            specs.push(ProofSpec { full: false, ..base });
            specs.push(ProofSpec { full: false, with_w0: true, ..base });
            specs.push(ProofSpec { u: UChoice::Same, ..base });
            specs.push(ProofSpec { src: Src::Rogue, ..base });
            specs.push(ProofSpec { src: Src::Other, ..base });
            specs.push(ProofSpec { wrong_parcel: true, ..base });
            if full {
                specs.push(ProofSpec { with_w0: true, ..base });
                specs.push(ProofSpec { u: UChoice::Same, with_w0: true, full: false, ..base });
                for i in 0..world.headers.len() {
                    specs.push(ProofSpec { u: UChoice::Header(i), ..base });
                    specs.push(ProofSpec { u: UChoice::Header(i), full: false, with_w0: true, ..base });
                }
            }
        }
    }
    for si in 0..world.sigils.len() {
        for spec in &specs {
            ops.push(Op::Release { si, spec: *spec });
        }
    }
    ops
}

static FILE_NO: AtomicU64 = AtomicU64::new(0);

fn tmp_path() -> std::path::PathBuf {
    let dir = if std::path::Path::new("/dev/shm").is_dir() { "/dev/shm".into() } else { std::env::temp_dir() };
    dir.join(format!("sigil-bfs-{}-{}.redb", std::process::id(), FILE_NO.fetch_add(1, Ordering::SeqCst)))
}

/// Run `op` on a witness restored from `st`; return the successor (records read back from the
/// store) and the checker's statistics.
fn expand(world: &World, st: &State, op: &Op) -> State {
    let path = tmp_path();
    let (store, _) = Store::open(&path).expect("store");
    let loaded = Loaded {
        pk: None,
        member: None,
        frozen: false,
        records: st.records.iter().map(|(k, v)| (k.clone(), v.clone())).collect::<HashMap<_, _>>(),
    };
    let clock = Arc::new(AtomicI64::new(NOW as i64));
    let w = open_witness(world, store.clone(), loaded, clock.clone());
    let mut c = Checker::with_witness(world, w, clock, st.shadow.clone());
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.step(op)));
    let shadow = c.shadow.clone();
    drop(c);
    store.close();
    drop(store);
    if let Err(e) = r {
        let _ = std::fs::remove_file(&path);
        std::panic::resume_unwind(e);
    }
    let (store2, written) = Store::open(&path).expect("reopen");
    drop(store2);
    let _ = std::fs::remove_file(&path);
    let mut records = st.records.clone();
    for (k, v) in written.records {
        records.insert(k, strip_log(&v));
    }
    // Hidden state = transcription.
    for (s, r) in &records {
        let rec = Record::from_json(r).expect("record");
        let sh = shadow.get(s).cloned().unwrap_or_default();
        let tix = |t: &str| world.headers.iter().position(|h| h.tid == t).map(|i| i as u32).unwrap_or(if t == "!contested" { CONTESTED } else { 999 });
        sigil_witness_proofs::model_eq!(rec.gen, sh.gen, "MODEL: stored gen of {s} after {op:?}");
        sigil_witness_proofs::model_eq!(rec.tid.as_deref().map(tix), sh.tid, "MODEL: stored tid after {op:?}");
        sigil_witness_proofs::model_eq!(rec.abstain, sh.abstain, "MODEL: stored abstain after {op:?}");
        let v = rec.vote.as_ref().map(|v| (v.get("gen").and_then(Json::as_int).unwrap(), tix(v.get("tid").and_then(Json::as_str).unwrap())));
        sigil_witness_proofs::model_eq!(v, sh.vote, "MODEL: stored vote of {s} after {op:?}");
        assert_eq!(rec.header.is_some(), rec.tid.is_some() && rec.tid.as_deref() != Some("!contested"), "header stored iff bound");
        if let (Some(h), Some(t)) = (&rec.header, &rec.tid) {
            sigil_witness_proofs::model_eq!(&sigil_witness::model::transition_id(h), t, "MODEL: stored header does not hash to the bound tid");
        }
    }
    State { records, shadow }
}

/// Initial states: the empty store, plus two a successor's ADOPT could write (Rust never
/// creates them, but it must handle them): `a` contested; `b` bound to t5 at gen 0 with
/// `abstain` because the key already voted t... at gen 0 (represented by a vote for t1's tid).
fn initial_states(world: &World, with_restored: bool) -> Vec<State> {
    let mut out = vec![State { records: BTreeMap::new(), shadow: BTreeMap::new() }];
    if with_restored {
        let a = &world.sigils[0].sigil;
        let b = &world.sigils[1].sigil;
        let contested = Record { gen: 0, tid: Some("!contested".into()), ..Default::default() };
        let mut records = BTreeMap::new();
        records.insert(a.clone(), contested.to_json());
        let mut shadow = BTreeMap::new();
        shadow.insert(a.clone(), RustRec { gen: 0, tid: Some(CONTESTED), ..Default::default() });
        // b: bound to t5 (b@0) while our key already voted t... "phantom" at gen 0.
        let k = world.w0_key();
        let other = sigil_witness_proofs::world::PHANTOM_TID;
        let old_vote = sigil_witness_proofs::world::signed_vote(&k, world.cid(0), 0, b, 0, other, 1);
        let abst = Record {
            gen: 0,
            tid: Some(world.headers[5].tid.clone()),
            header: Some(world.headers[5].header.clone()),
            vote: None,
            log: vec![],
            votes: vec![old_vote],
            abstain: true,
        };
        records.insert(b.clone(), abst.to_json());
        shadow.insert(b.clone(), RustRec { gen: 0, tid: Some(5), vote: None, abstain: true, votes: vec![(0, 10_000)] });
        out.push(State { records, shadow });
    }
    out
}

fn bfs(world: &World, ops: &[Op], init: Vec<State>, threads: usize) -> (usize, usize, usize) {
    let mut seen: HashSet<Key> = HashSet::new();
    let mut frontier: Vec<State> = Vec::new();
    for s in init {
        if seen.insert(s.key()) {
            frontier.push(s);
        }
    }
    let mut transitions = 0usize;
    let mut depth = 0usize;
    while !frontier.is_empty() {
        let chunk = frontier.len().div_ceil(threads);
        let results: Vec<Vec<State>> = std::thread::scope(|sc| {
            let hs: Vec<_> = frontier
                .chunks(chunk)
                .map(|part| sc.spawn(move || part.iter().flat_map(|st| ops.iter().map(move |op| expand(world, st, op))).collect::<Vec<_>>()))
                .collect();
            hs.into_iter().map(|h| h.join().expect("worker panicked: see the message above")).collect()
        });
        transitions += frontier.len() * ops.len();
        let mut next = Vec::new();
        for s in results.into_iter().flatten() {
            if seen.insert(s.key()) {
                next.push(s);
            }
        }
        frontier = next;
        depth += 1;
        eprintln!("bfs depth {depth}: {} states, {} new, {transitions} transitions", seen.len(), frontier.len());
    }
    (seen.len(), transitions, depth)
}

#[test]
fn real_witness_refines_tla_spend_release() {
    let full = std::env::var("SIGIL_BFS_FULL").is_ok();
    let world = World::new(&default_headers());
    let ops = alphabet(&world, full);
    let t = std::time::Instant::now();
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(2);
    let (states, transitions, depth) = bfs(&world, &ops, initial_states(&world, true), threads);
    eprintln!(
        "RESULT: alphabet {} ops, {} distinct states, {} checked transitions, depth {}, {:.1}s",
        ops.len(),
        states,
        transitions,
        depth,
        t.elapsed().as_secs_f64()
    );
    assert!(states > 10);
}
