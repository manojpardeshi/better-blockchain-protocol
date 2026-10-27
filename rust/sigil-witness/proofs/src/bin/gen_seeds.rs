//! Write seed corpora for the byte-level fuzz targets.
//!
//!     cargo run --release --bin gen_seeds -- ../fuzz/corpus
//!
//! * `json_roundtrip/`: the inputs of tests/vectors.json "canonical" plus protocol messages;
//! * `witness_http_body/`: message sequences (spend, then releases and statuses) in the
//!   target's framing: method byte, body, 0x00 separator.

use std::fs;
use std::path::Path;

use sigil_witness::json::{obj, parse, Json};
use sigil_witness_proofs::checker::Checker;
use sigil_witness_proofs::world::{default_headers, ProofSpec, Src, UChoice, World};

fn write(dir: &Path, name: &str, bytes: &[u8]) {
    fs::create_dir_all(dir).expect("mkdir");
    fs::write(dir.join(name), bytes).expect("write");
}

fn main() {
    let out = std::env::args().nth(1).unwrap_or_else(|| "../fuzz/corpus".into());
    let out = Path::new(&out);
    let world = World::new(&default_headers());

    // json_roundtrip
    let jdir = out.join("json_roundtrip");
    let vectors = fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/vectors.json")).expect("vectors.json");
    let v = parse(&vectors).expect("parse vectors");
    let mut n = 0;
    for c in v.get("canonical").and_then(Json::as_arr).expect("canonical") {
        if n % 7 == 0 {
            write(&jdir, &format!("vec{n}"), c.get("json").and_then(Json::as_str).expect("json").as_bytes());
        }
        n += 1;
    }
    for (i, hi) in [0usize, 2, 4].iter().enumerate() {
        write(&jdir, &format!("req{i}"), world.spend_request(0, *hi, true, false).canonical_string().as_bytes());
    }

    // witness_http_body: spend a in t_hi, then a release with a valid proof, then status.
    let hdir = out.join("witness_http_body");
    let mut k = 0;
    for hi in [0usize, 2, 3, 4, 6] {
        let si = 0;
        let req = world.spend_request(si, hi, true, false);
        let mut c = Checker::new(&world);
        let _ = c.w.spend(&req);
        for (j, spec) in [
            ProofSpec { k: 0, seal: true, src: Src::Home, u: UChoice::Phantom, full: true, with_w0: false, wrong_parcel: false },
            ProofSpec { k: 1, seal: false, src: Src::Home, u: UChoice::Phantom, full: true, with_w0: false, wrong_parcel: false },
            ProofSpec { k: 0, seal: true, src: Src::Rogue, u: UChoice::Phantom, full: true, with_w0: false, wrong_parcel: false },
        ]
        .iter()
        .enumerate()
        {
            let (sigil, proof) = c.build_release_proof(si, spec);
            let mut bytes = Vec::new();
            bytes.push(0u8);
            bytes.extend(obj([("request", req.clone())]).canonical());
            bytes.push(0);
            bytes.push(1);
            bytes.extend(obj([("sigil", Json::str(&sigil)), ("proof", proof)]).canonical());
            bytes.push(0);
            bytes.push(2);
            bytes.extend(obj([("sigil", Json::str(&sigil))]).canonical());
            let next = world.spend_request(si, 3, true, false);
            bytes.push(0);
            bytes.push(0);
            bytes.extend(obj([("request", next)]).canonical());
            write(&hdir, &format!("seq{k}-{j}"), &bytes);
        }
        k += 1;
    }
    eprintln!("seeds written under {}", out.display());
}
