//! Raw HTTP bodies, handled as `server::call` does (parse, object check, field extraction),
//! then checked like `witness_ops`. Input: messages separated by 0x00; each is one method byte
//! (0 spend, 1 release, 2 status, 3 unknown) followed by the body.
#![no_main]
use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use sigil_witness::json::{parse, Json};
use sigil_witness_proofs::checker::Checker;
use sigil_witness_proofs::world::{default_headers, World};

static WORLD: OnceLock<World> = OnceLock::new();

fuzz_target!(|data: &[u8]| {
    let world = WORLD.get_or_init(|| World::new(&default_headers()));
    let mut c = Checker::new(world);
    c.check_completeness = false;
    for msg in data.split(|b| *b == 0).take(8) {
        let Some((&method, body)) = msg.split_first() else { continue };
        if cfg!(feature = "skip_known_bugs") && sigil_witness_proofs::fuzzgen::hits_known_parser_panic(body) {
            continue;
        }
        let body = if body.is_empty() {
            Json::Obj(Default::default())
        } else {
            match parse(body) {
                Ok(v) => v,
                Err(_) => continue,
            }
        };
        if body.as_obj().is_none() {
            continue;
        }
        match method % 4 {
            0 => {
                if let Some(req) = body.get("request") {
                    let sigil = req.get("sigil").and_then(Json::as_str).unwrap_or("").to_string();
                    c.do_spend(&sigil, req, None);
                }
            }
            1 => {
                if let (Some(s), Some(p)) = (body.get("sigil"), body.get("proof")) {
                    c.do_release_raw(s, p);
                }
            }
            2 => {
                if let Some(s) = body.get("sigil") {
                    c.do_status_raw(s);
                }
            }
            _ => {}
        }
    }
});
