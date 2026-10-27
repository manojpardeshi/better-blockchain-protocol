//! Sequences of SPEND / RELEASE / STATUS against a real witness, every step checked by
//! `Checker` (no panic, one tid per (sigil, gen), TLA+ refinement, transcription, death-proof
//! soundness). Structured ops use well-formed requests; raw ops mutate them arbitrarily.
#![no_main]
use std::sync::atomic::Ordering;
use std::sync::OnceLock;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sigil_witness::json::Json;
use sigil_witness_proofs::checker::{Checker, Op};
use sigil_witness_proofs::fuzzgen::{mutate, FVal, Mutation, Pool};
use sigil_witness_proofs::world::{default_headers, ProofSpec, Src, UChoice, World, NOW};

#[derive(Arbitrary, Debug)]
struct FSpec {
    k: u8,
    seal: bool,
    src: u8,
    u: u8,
    full: bool,
    with_w0: bool,
    wrong_parcel: bool,
}

impl FSpec {
    fn spec(&self) -> ProofSpec {
        ProofSpec {
            k: self.k as usize,
            seal: self.seal,
            src: [Src::Home, Src::Home, Src::Rogue, Src::Other][self.src as usize % 4],
            u: match self.u % 4 {
                0 | 1 => UChoice::Phantom,
                2 => UChoice::Same,
                _ => UChoice::Header(self.u as usize / 4),
            },
            full: self.full,
            with_w0: self.with_w0,
            wrong_parcel: self.wrong_parcel,
        }
    }
}

#[derive(Arbitrary, Debug)]
enum FOp {
    Spend { si: u8, hi: u8, lock_ok: bool, expired: bool, later: bool },
    Release { si: u8, spec: FSpec },
    Status { si: u8 },
    RawSpend { si: u8, hi: u8, expired: bool, muts: Vec<Mutation>, clock: i16 },
    RawRelease { si: u8, spec: FSpec, muts: Vec<Mutation> },
    RawReleaseSigil(FVal),
    RawStatus(FVal),
}

static WORLD: OnceLock<(World, Pool)> = OnceLock::new();

fuzz_target!(|ops: Vec<FOp>| {
    let (world, pool) = WORLD.get_or_init(|| {
        let w = World::new(&default_headers());
        let p = Pool::new(&w);
        (w, p)
    });
    let ns = world.sigils.len();
    let nh = world.headers.len();
    let mut c = Checker::new(world);
    for op in ops.iter().take(48) {
        match op {
            FOp::Spend { si, hi, lock_ok, expired, later } => c.step(&Op::Spend {
                si: *si as usize % ns,
                hi: *hi as usize % nh,
                lock_ok: *lock_ok,
                expired: *expired,
                later: *later,
            }),
            FOp::Release { si, spec } => c.step(&Op::Release { si: *si as usize % ns, spec: spec.spec() }),
            FOp::Status { si } => c.step(&Op::Status { si: *si as usize % ns }),
            FOp::RawSpend { si, hi, expired, muts, clock } => {
                let si = *si as usize % ns;
                let mut req = world.spend_request(si, *hi as usize % nh, true, *expired);
                for m in muts.iter().take(4) {
                    mutate(&mut req, m, pool);
                }
                let sigil = req.get("sigil").and_then(Json::as_str).unwrap_or(&world.sigils[si].sigil).to_string();
                c.clock.store(NOW as i64 + *clock as i64, Ordering::SeqCst);
                c.do_spend(&sigil, &req, None);
            }
            FOp::RawRelease { si, spec, muts } => {
                let (sigil, mut proof) = c.build_release_proof(*si as usize % ns, &spec.spec());
                for m in muts.iter().take(4) {
                    mutate(&mut proof, m, pool);
                }
                c.do_release_raw(&Json::Str(sigil), &proof);
            }
            FOp::RawReleaseSigil(v) => c.do_release_raw(&pool.json(v, 0), &Json::Null),
            FOp::RawStatus(v) => c.do_status_raw(&pool.json(v, 0)),
        }
    }
});
