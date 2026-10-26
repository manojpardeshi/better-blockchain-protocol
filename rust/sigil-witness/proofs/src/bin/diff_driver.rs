//! JSON-lines driver for the differential test against the Python reference
//! (proofs/diff/differential.py). One request per line on stdin, one reply per line on stdout.
//!
//! ```text
//! {"op":"init","registry":{..},"cid":"..","py_seed":"<hex>"}       -> {"ok":true}
//! {"op":"spend","now":N,"args":[request]}                           -> outcome
//! {"op":"release","now":N,"args":[sigil, proof]}                    -> outcome
//! {"op":"status","now":N,"args":[sigil]}                            -> outcome
//! {"op":"canonical","args":[text]}       -> {"ok": canonical text} | {"error":"bad_request"}
//! outcome = {"ok":x} | {"error":"conflict","vote":v} | {"error":"rejected","message":m}
//!         | {"error":"bad_request"} | {"error":"panic","message":m}
//! ```
//!
//! The witness is the real `sigil_witness::Witness` with an in-memory store, its clock set from
//! `now` before every call. Request values reach it exactly as `server::call` passes them:
//! lines are parsed with `sigil_witness::json::parse`.

use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

use sigil_witness::charter::Registry;
use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{obj, parse, Json};
use sigil_witness::store::{Loaded, Store};
use sigil_witness::witness::{Error, Witness};

fn outcome(r: Result<Json, Error>) -> Json {
    match r {
        Ok(v) => obj([("ok", v)]),
        Err(Error::Conflict(v)) => obj([("error", Json::str("conflict")), ("vote", v.unwrap_or(Json::Null))]),
        Err(Error::Rejected(m)) => obj([("error", Json::str("rejected")), ("message", Json::str(m))]),
        Err(Error::BadRequest(m)) => obj([("error", Json::str("bad_request")), ("message", Json::str(m))]),
    }
}

fn main() {
    let stdin = std::io::stdin();
    let mut out = std::io::BufWriter::new(std::io::stdout());
    let clock = Arc::new(AtomicI64::new(0));
    let mut w: Option<Witness> = None;
    std::panic::set_hook(Box::new(|_| {}));
    for line in stdin.lock().lines() {
        let line = line.expect("stdin");
        let reply = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Json {
            let msg = match parse(line.as_bytes()) {
                Ok(m) => m,
                Err(e) => return obj([("error", Json::str("bad_request")), ("message", Json::str(format!("parse: {e}")))]),
            };
            let args = msg.get("args").and_then(Json::as_arr).cloned().unwrap_or_default();
            let arg = |i: usize| args.get(i).cloned().unwrap_or(Json::Null);
            if let Some(n) = msg.get("now").and_then(Json::as_int) {
                clock.store(n as i64, Ordering::SeqCst);
            }
            match msg.get("op").and_then(Json::as_str).unwrap_or("") {
                "init" => {
                    let reg = Registry::from_json(msg.get("registry").expect("registry")).expect("registry");
                    let seed = hex::decode(msg.get("py_seed").and_then(Json::as_str).expect("seed")).expect("hex");
                    let kp = KeyPair::from_py_seed(&seed);
                    let c2 = clock.clone();
                    let cid = msg.get("cid").and_then(Json::as_str).expect("cid");
                    w = Some(
                        Witness::open(kp, reg, cid, Store::memory(), Loaded::default(), Box::new(move || c2.load(Ordering::SeqCst) as i128))
                            .expect("open"),
                    );
                    obj([("ok", Json::Bool(true))])
                }
                "spend" => outcome(w.as_ref().expect("init first").spend(&arg(0)).0),
                "release" => outcome(w.as_ref().expect("init first").release(&arg(0), &arg(1)).0),
                "status" => outcome(w.as_ref().expect("init first").status(&arg(0)).0),
                "canonical" => match arg(0).as_str().map(|t| parse(t.as_bytes())) {
                    Some(Ok(v)) => obj([("ok", Json::Str(v.canonical_string()))]),
                    _ => obj([("error", Json::str("bad_request"))]),
                },
                _ => obj([("error", Json::str("bad_request"))]),
            }
        }));
        let reply = reply.unwrap_or_else(|_| obj([("error", Json::str("panic")), ("message", Json::str("panicked"))]));
        out.write_all(&reply.canonical()).expect("stdout");
        out.write_all(b"\n").expect("stdout");
        out.flush().expect("stdout");
    }
}
