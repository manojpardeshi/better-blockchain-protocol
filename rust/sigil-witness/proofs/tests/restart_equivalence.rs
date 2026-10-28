//! Restart equivalence: a witness that is closed and re-opened from its durable store after
//! EVERY step (with the records' write-only `log` dropped, as refinement_bfs.rs does) gives
//! byte-identical replies to one that runs continuously, over random op sequences.
//!
//! This checks (a) persist-before-answer leaves nothing in memory only that a reply depends
//! on, and (b) the `log` field never influences a reply, which justifies the state identity used
//! by the bounded exhaustive refinement check.

use std::collections::HashMap;
use std::sync::atomic::AtomicI64;
use std::sync::Arc;

use sigil_witness::json::Json;
use sigil_witness::store::{Loaded, Store};
use sigil_witness::witness::Witness;
use sigil_witness_proofs::checker::{open_witness, strip_log};
use sigil_witness_proofs::world::{default_headers, Genuine, ProofSpec, Src, UChoice, World, NOW};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

fn reply(r: Result<Json, sigil_witness::witness::Error>) -> String {
    format!("{r:?}")
}

fn reopen(world: &World, path: &std::path::Path) -> (Witness, Arc<Store>) {
    let (store, loaded) = Store::open(path).expect("store");
    let records: HashMap<String, Json> = loaded.records.iter().map(|(k, v)| (k.clone(), strip_log(v))).collect();
    let loaded = Loaded { records, ..loaded };
    let w = open_witness(world, store.clone(), loaded, Arc::new(AtomicI64::new(NOW as i64)));
    (w, store)
}

#[test]
fn restart_after_every_step_changes_no_reply() {
    let world = World::new(&default_headers());
    let dir = std::env::temp_dir().join(format!("sigil-restart-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut steps = 0;
    for seed in 1..=12u64 {
        let path = dir.join(format!("w{seed}.redb"));
        let _ = std::fs::remove_file(&path);
        let mut rng = Rng(seed * 0x9e3779b97f4a7c15);
        let continuous = open_witness(&world, Store::memory(), Loaded::default(), Arc::new(AtomicI64::new(NOW as i64)));
        let mut genuine = Genuine::default();
        for _ in 0..60 {
            let (restarted, store) = reopen(&world, &path);
            let si = rng.below(world.sigils.len());
            let sigil = Json::str(&world.sigils[si].sigil);
            let (a, b) = match rng.below(3) {
                0 => {
                    let req = world.spend_request(si, rng.below(world.headers.len()), rng.below(5) != 0, rng.below(6) == 0);
                    (reply(continuous.spend(&req).0), reply(restarted.spend(&req).0))
                }
                1 => {
                    let st = continuous.status(&sigil).0.unwrap();
                    let ht = st
                        .get("tid")
                        .and_then(Json::as_str)
                        .and_then(|t| world.headers.iter().position(|h| h.tid == t))
                        .unwrap_or(0);
                    let spec = ProofSpec {
                        k: rng.below(2),
                        seal: rng.coin(),
                        src: [Src::Home, Src::Home, Src::Rogue, Src::Other][rng.below(4)],
                        u: [UChoice::Phantom, UChoice::Same][rng.below(2)],
                        full: rng.below(4) != 0,
                        with_w0: rng.coin(),
                        wrong_parcel: rng.below(8) == 0,
                    };
                    let w0 = |s: usize| {
                        continuous.status(&Json::str(&world.sigils[s].sigil)).0.ok()
                            .and_then(|r| r.get("votes").and_then(Json::as_arr).cloned())
                            .unwrap_or_default()
                    };
                    let proof = world.build_proof(&spec, ht, &w0, &mut genuine);
                    (reply(continuous.release(&sigil, &proof).0), reply(restarted.release(&sigil, &proof).0))
                }
                _ => (reply(continuous.status(&sigil).0), reply(restarted.status(&sigil).0)),
            };
            assert_eq!(a, b, "seed {seed}: reply differs after a restart");
            steps += 1;
            store.close();
            drop(restarted);
        }
        // Final state agrees on every sigil.
        let (restarted, store) = reopen(&world, &path);
        for s in &world.sigils {
            let j = Json::str(&s.sigil);
            assert_eq!(reply(continuous.status(&j).0), reply(restarted.status(&j).0));
        }
        store.close();
    }
    let _ = std::fs::remove_dir_all(&dir);
    eprintln!("RESULT: {steps} steps, each on a freshly re-opened witness, identical replies");
}
