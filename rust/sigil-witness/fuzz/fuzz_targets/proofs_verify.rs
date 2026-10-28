//! Seal, death-proof and equivocation-proof verification on mutated proofs: no panic; batch
//! and single verification agree; every accepted proof is valid per a spec-level oracle that
//! counts only genuinely signed votes; votes_of_seal never lets an entry override the seal.
#![no_main]
use std::collections::HashSet;
use std::sync::OnceLock;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sigil_witness::charter::Registry;
use sigil_witness::json::{obj, Json};
use sigil_witness::proofs::{proves_dead, verify_equivocation, verify_seal, votes_of_seal};
use sigil_witness_proofs::fuzzgen::{mutate, Mutation, Pool};
use sigil_witness_proofs::world::{default_headers, signed_vote, Genuine, ProofSpec, Src, UChoice, World, C, NOW, PHANTOM_TID};

#[derive(Arbitrary, Debug)]
struct Case {
    ht: u8,
    k: u8,
    seal: bool,
    src: u8,
    u: u8,
    full: bool,
    with_w0: bool,
    wrong_parcel: bool,
    muts: Vec<Mutation>,
    eq: (u8, u8, u8, u8),
    eq_muts: Vec<Mutation>,
}

static CTX: OnceLock<(World, Pool, Registry)> = OnceLock::new();

fuzz_target!(|case: Case| {
    let (world, pool, reg) = CTX.get_or_init(|| {
        let w = World::new(&default_headers());
        let p = Pool::new(&w);
        let r = Registry::from_json(&w.registry).expect("registry");
        (w, p, r)
    });
    let ht = case.ht as usize % world.headers.len();
    let spec = ProofSpec {
        k: case.k as usize,
        seal: case.seal,
        src: [Src::Home, Src::Home, Src::Rogue, Src::Other][case.src as usize % 4],
        u: match case.u % 3 {
            0 => UChoice::Phantom,
            1 => UChoice::Same,
            _ => UChoice::Header(case.u as usize / 3),
        },
        full: case.full,
        with_w0: case.with_w0,
        wrong_parcel: case.wrong_parcel,
    };
    let mut genuine = Genuine::default();
    // w0's key also signs here (no witness runs in this target): one vote per (sigil, gen).
    let w0 = world.w0_key();
    let w0_votes: Vec<Vec<Json>> = world
        .sigils
        .iter()
        .map(|s| (0..3).map(|g| signed_vote(&w0, world.cid(C), 0, &s.sigil, g, PHANTOM_TID, NOW)).collect())
        .collect();
    for v in w0_votes.iter().flatten() {
        genuine.add(v);
    }
    let f = |s: usize| w0_votes[s].clone();
    let mut proof = world.build_proof(&spec, ht, &f, &mut genuine);
    for m in case.muts.iter().take(6) {
        mutate(&mut proof, m, pool);
    }
    let h = &world.headers[ht];
    let d1 = proves_dead(&h.header, &h.tid, &proof, reg, false);
    let d2 = proves_dead(&h.header, &h.tid, &proof, reg, true);
    assert_eq!(d1, d2, "batch verification changed a death-proof verdict");
    if d1 {
        assert!(world.oracle_dead(&h.header, &h.tid, &proof, &genuine).0, "accepted an invalid death proof: {}", proof.canonical_string());
    }
    if let Some(seal) = proof.get("seal") {
        let none = HashSet::new();
        let s1 = verify_seal(seal, reg, &none, false);
        assert_eq!(s1, verify_seal(seal, reg, &none, true), "batch verification changed a seal verdict");
        if s1 {
            assert!(world.oracle_seal(seal, &genuine), "accepted an invalid seal: {}", seal.canonical_string());
        }
        if let Some(vs) = votes_of_seal(seal) {
            for v in &vs {
                for k in ["constellation", "version", "sigil", "gen", "tid"] {
                    assert_eq!(v.get(k), seal.get(k), "a seal entry overrode the seal's {k}");
                }
            }
        }
    }
    // Equivocation proofs from a small set of genuine votes.
    let keys = &world.cons[C].keys;
    let tids = [world.headers[0].tid.as_str(), world.headers[1].tid.as_str()];
    let mk = |kk: u8, t: u8| {
        signed_vote(&keys[kk as usize % 4], world.cid(C), 0, &world.sigils[0].sigil, (t / 2 % 2) as i128, tids[t as usize % 2], NOW)
    };
    let (a, b) = (mk(case.eq.0, case.eq.1), mk(case.eq.2, case.eq.3));
    genuine.add(&a);
    genuine.add(&b);
    let mut p = obj([("a", a), ("b", b)]);
    for m in case.eq_muts.iter().take(4) {
        mutate(&mut p, m, pool);
    }
    let e1 = verify_equivocation(&p, false);
    assert_eq!(e1, verify_equivocation(&p, true), "batch verification changed an equivocation verdict");
    if e1 {
        let (a, b) = (p.get("a").expect("a"), p.get("b").expect("b"));
        assert!(genuine.contains(a) && genuine.contains(b), "equivocation proof with a non-genuine vote");
        for k in ["witness", "constellation", "sigil", "gen"] {
            assert_eq!(a.get(k), b.get(k), "equivocation proof votes differ in {k}");
        }
        assert_ne!(a.get("tid"), b.get("tid"));
    }
});
