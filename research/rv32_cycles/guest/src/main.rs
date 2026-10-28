//! The Sigil PCD step relation, as a bare-metal RV32IM program.
//!
//! This is what a zkVM guest (SP1, RISC Zero, Jolt) would execute for one
//! transition: SPEC §6 for the transition itself, plus folding the public
//! statements of the parents' proofs (research/pcd.py, `step`). It runs in
//! the instruction-counting emulator in ../emu, which stands in for a zkVM
//! executor: the instruction count is (close to) the cycle count a zkVM
//! would prove, without precompiles.
//!
//! Input: a JSON witness at the address in a0 (length in a1), produced by
//! ../make_witness.py. Output (to stdout): the statement digest, which must
//! equal the Python reference's, and an instruction breakdown by category.
//! What it does NOT do: verify the children's proofs (a zkVM guest would
//! call its recursion syscall on each child statement digest; that cost is
//! the proving system's, not the program's).

#![no_std]
#![no_main]

extern crate alloc;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use core::arch::global_asm;

use blake2::digest::{Update, VariableOutput};
use blake2::Blake2bVar;
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use serde_json::{json, Map, Value};

// ------------------------------------------------------------------ runtime

global_asm!(
    ".section .text.init",
    ".global _start",
    "_start:",
    "  la sp, __stack_top",
    "  call guest_main",
    "  li a7, 93",
    "  ecall",
);

extern "C" {
    static __heap_start: u8;
}

struct Bump;
static mut NEXT: usize = 0;
const HEAP_END: usize = 0x0380_0000;

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if NEXT == 0 {
            NEXT = core::ptr::addr_of!(__heap_start) as usize;
        }
        let p = (NEXT + l.align() - 1) & !(l.align() - 1);
        if p + l.size() > HEAP_END {
            exit(3);
        }
        NEXT = p + l.size();
        p as *mut u8
    }
    unsafe fn dealloc(&self, _p: *mut u8, _l: Layout) {}
}

#[global_allocator]
static ALLOC: Bump = Bump;

fn ecall(n: u32, a0: u32, a1: u32, a2: u32) -> (u32, u32) {
    let (r0, r1);
    unsafe {
        core::arch::asm!("ecall", in("a7") n, inlateout("a0") a0 => r0, inlateout("a1") a1 => r1, in("a2") a2);
    }
    (r0, r1)
}

fn exit(code: u32) -> ! {
    ecall(93, code, 0, 0);
    loop {}
}

fn print(s: &str) {
    ecall(64, 1, s.as_ptr() as u32, s.len() as u32);
}

fn instret() -> u64 {
    let (lo, hi) = ecall(0x1000, 0, 0, 0);
    (hi as u64) << 32 | lo as u64
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    print(&format!("panic: {info}\n"));
    exit(101)
}

// ----------------------------------------------------------------- profiling

const CATS: [&str; 5] = ["parse", "encode", "blake2b", "ed25519", "logic"];
static mut SPENT: [u64; 5] = [0; 5];
static mut STACK: [usize; 16] = [4; 16];
static mut DEPTH: usize = 0;
static mut MARK: u64 = 0;
static mut COUNTS: [u64; 3] = [0; 3]; // hashes, bytes hashed, signatures

/// Attribute instructions to a category (nested calls charge the innermost).
fn timed<T>(cat: usize, f: impl FnOnce() -> T) -> T {
    unsafe {
        let now = instret();
        SPENT[STACK[DEPTH]] += now - MARK;
        MARK = now;
        DEPTH += 1;
        STACK[DEPTH] = cat;
        let r = f();
        let now = instret();
        SPENT[cat] += now - MARK;
        MARK = now;
        DEPTH -= 1;
        r
    }
}

// --------------------------------------------------------------- primitives

fn hex(b: &[u8]) -> String {
    const H: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        s.push(H[(x >> 4) as usize] as char);
        s.push(H[(x & 15) as usize] as char);
    }
    s
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    let v = |c: u8| match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    };
    s.as_bytes().chunks(2).map(|p| Some(v(p[0])? << 4 | v(p[1])?)).collect()
}

/// enc(x): JSON with sorted keys and no whitespace (serde_json's map is a
/// BTreeMap here, so keys come out sorted, as Python's sort_keys does).
fn canonical(x: &Value) -> Vec<u8> {
    timed(1, || serde_json::to_vec(x).expect("encodable"))
}

fn blake2b256(parts: &[&[u8]]) -> [u8; 32] {
    timed(2, || {
        let mut h = Blake2bVar::new(32).unwrap();
        let mut n = 0;
        for p in parts {
            h.update(p);
            n += p.len();
        }
        unsafe {
            COUNTS[0] += 1;
            COUNTS[1] += n as u64;
        }
        let mut out = [0u8; 32];
        h.finalize_variable(&mut out).unwrap();
        out
    })
}

/// H(tag, x) = BLAKE2b-256("sigil/v0/" ‖ tag ‖ 0x00 ‖ enc(x)), hex.
fn digest(tag: &str, x: &Value) -> String {
    let enc = canonical(x);
    hex(&blake2b256(&[b"sigil/v0/", tag.as_bytes(), b"\0", &enc]))
}

/// Ed25519 over "sigil/v0/sig/" ‖ tag ‖ 0x00 ‖ enc(x).
fn verify(pk: &str, tag: &str, x: &Value, sig: &str) -> bool {
    let enc = canonical(x);
    let mut msg = Vec::with_capacity(enc.len() + 32);
    msg.extend_from_slice(b"sigil/v0/sig/");
    msg.extend_from_slice(tag.as_bytes());
    msg.push(0);
    msg.extend_from_slice(&enc);
    let (Some(pk), Some(sig)) = (unhex(pk), unhex(sig)) else { return false };
    let (Ok(pk), Ok(sig)) = (<[u8; 32]>::try_from(pk), <[u8; 64]>::try_from(sig)) else { return false };
    timed(3, || {
        unsafe { COUNTS[2] += 1 };
        match VerifyingKey::from_bytes(&pk) {
            Ok(vk) => vk.verify(&msg, &Signature::from_bytes(&sig)).is_ok(),
            Err(_) => false,
        }
    })
}

// ------------------------------------------------------------------- model

fn fail(why: &str) -> ! {
    print(&format!("INVALID {why}\n"));
    exit(1)
}

fn s<'a>(v: &'a Value, k: &str) -> &'a str {
    v.get(k).and_then(Value::as_str).unwrap_or_else(|| fail("expected a string"))
}

fn int(v: &Value) -> Option<i64> {
    v.as_i64()
}

fn amount(v: &Value) -> Option<u128> {
    v.as_u64().filter(|&x| x > 0).map(|x| x as u128)
}

fn keys_are(v: &Value, keys: &[&str]) -> bool {
    v.as_object().map_or(false, |m| m.len() == keys.len() && keys.iter().all(|k| m.contains_key(*k)))
}

fn well_formed(lock: &Value, depth: usize, budget: &mut i32) -> bool {
    *budget -= 1;
    if *budget < 0 || depth > 8 || !lock.is_object() {
        return false;
    }
    let str_ = |k: &str| lock.get(k).map_or(false, Value::is_string);
    let int_ = |k: &str| lock.get(k).map_or(false, |x| x.is_i64() || x.is_u64());
    match lock.get("op").and_then(Value::as_str) {
        Some("sig") => keys_are(lock, &["op", "pk"]) && str_("pk"),
        Some("multi") => {
            let Some(pks) = lock.get("pks").and_then(Value::as_array) else { return false };
            let k = lock.get("k").and_then(Value::as_i64).unwrap_or(0);
            let uniq: BTreeSet<_> = pks.iter().filter_map(Value::as_str).collect();
            keys_are(lock, &["op", "k", "pks"]) && k >= 1 && k as usize <= pks.len() && uniq.len() == pks.len()
        }
        Some("after") | Some("before") => keys_are(lock, &["op", "t"]) && int_("t"),
        Some("hash") => keys_are(lock, &["op", "h"]) && str_("h"),
        Some("equivocation") => keys_are(lock, &["op", "witness"]) && str_("witness"),
        Some("all") | Some("any") => {
            let Some(of) = lock.get("of").and_then(Value::as_array) else { return false };
            keys_are(lock, &["op", "of"]) && !of.is_empty() && of.iter().all(|x| well_formed(x, depth + 1, budget))
        }
        Some("never") => keys_are(lock, &["op"]),
        _ => false,
    }
}

fn parcel_ok(o: &Value) -> bool {
    keys_are(o, &["home", "asset", "amount", "lock", "salt"])
        && o["home"].is_string() && o["asset"].is_string() && o["salt"].is_string()
        && amount(&o["amount"]).is_some()
        && well_formed(&o["lock"], 0, &mut 64)
}

const VOTE_FIELDS: [&str; 7] = ["constellation", "version", "witness", "sigil", "gen", "tid", "time"];

fn vote_ok(v: &Value) -> bool {
    let mut payload = Map::new();
    for k in VOTE_FIELDS {
        match v.get(k) {
            Some(x) => payload.insert(k.to_string(), x.clone()),
            None => return false,
        };
    }
    match (v.get("witness").and_then(Value::as_str), v.get("sig").and_then(Value::as_str)) {
        (Some(w), Some(sig)) => verify(w, "vote", &Value::Object(payload), sig),
        _ => false,
    }
}

fn equivocation_ok(p: &Value) -> bool {
    let (Some(a), Some(b)) = (p.get("a"), p.get("b")) else { return false };
    ["witness", "constellation", "sigil", "gen"].iter().all(|k| a.get(*k).is_some() && a.get(*k) == b.get(*k))
        && a.get("tid") != b.get("tid") && vote_ok(a) && vote_ok(b)
}

/// eval(lock, unlock, sigil, tid, now = null): holders treat time locks as satisfied.
fn evaluate(lock: &Value, unlock: &Value, sigil: &str, tid: &str) -> bool {
    if !well_formed(lock, 0, &mut 64) || !unlock.is_object() {
        return false;
    }
    let msg = json!({"sigil": sigil, "tid": tid, "expires": unlock.get("expires").cloned().unwrap_or(Value::Null)});
    let empty = Map::new();
    let sigs = unlock.get("sigs").and_then(Value::as_object).unwrap_or(&empty);
    let pres = unlock.get("preimages").and_then(Value::as_object).unwrap_or(&empty);
    let eqs: &[Value] = unlock.get("equivocations").and_then(Value::as_array).map_or(&[], |v| v.as_slice());
    let has_sig = |pk: &str| sigs.get(pk).and_then(Value::as_str).map_or(false, |sg| verify(pk, "unlock", &msg, sg));
    fn ev(n: &Value, has_sig: &dyn Fn(&str) -> bool, pres: &Map<String, Value>, eqs: &[Value]) -> bool {
        match n["op"].as_str().unwrap_or("") {
            "sig" => has_sig(n["pk"].as_str().unwrap_or("")),
            "multi" => {
                let k = n["k"].as_u64().unwrap_or(u64::MAX) as usize;
                n["pks"].as_array().unwrap().iter().filter(|pk| has_sig(pk.as_str().unwrap_or(""))).count() >= k
            }
            "after" | "before" => true,
            "hash" => {
                let h = n["h"].as_str().unwrap_or("");
                pres.get(h).and_then(Value::as_str).and_then(unhex).map_or(false, |pre| hex(&blake2b256(&[&pre])) == h)
            }
            "equivocation" => eqs.iter().any(|p| p.get("a").and_then(|a| a.get("witness")) == Some(&n["witness"]) && equivocation_ok(p)),
            "all" => n["of"].as_array().unwrap().iter().all(|x| ev(x, has_sig, pres, eqs)),
            "any" => n["of"].as_array().unwrap().iter().any(|x| ev(x, has_sig, pres, eqs)),
            _ => false,
        }
    }
    ev(lock, &has_sig, pres, eqs)
}

fn resolve_asset(asset: &str, tid: &str) -> String {
    match asset {
        "" => tid.to_string(),
        "mint:" => format!("mint:{tid}"),
        a => a.to_string(),
    }
}

fn output_commitment(tid: &str, i: usize, parcel: &Value) -> String {
    digest("pcd-output", &json!({"ref": {"tx": tid, "i": i}, "parcel": parcel}))
}

fn sigil_of(p: &Value) -> String {
    digest("sigil", &json!({"home": p["home"], "lock": p["lock"], "salt": p["salt"]}))
}

fn quorum(n: usize) -> usize {
    n - (n - 1) / 3
}

// -------------------------------------------------------------------- step

struct Relied {
    charter: String,
    slack: i64,
}

fn step(w: &Value) -> Value {
    let tid = s(w, "tid");
    let h = &w["header"];
    let b = &w["body"];
    let unlocks = &w["unlocks"];
    // 1. hashes
    if digest("transition", h) != tid || digest("body", b) != s(h, "body") {
        fail("transition does not match its id");
    }
    // 2. outputs
    let outs = b["outputs"].as_array().unwrap_or_else(|| fail("outputs"));
    if outs.is_empty() || !outs.iter().all(parcel_ok) {
        fail("malformed output");
    }
    let commitments: Vec<Value> = outs.iter().enumerate().map(|(i, o)| {
        let mut p = o.clone();
        p["asset"] = Value::String(resolve_asset(s(o, "asset"), tid));
        Value::String(output_commitment(tid, i, &p))
    }).collect();
    let step_id = s(w, "step_id");
    let statement = |relied: Value, excluded: Value, confirmed: Value| {
        json!({"v": step_id, "tid": tid, "outputs": commitments.clone(), "relied": relied, "excluded": excluded, "confirmed": confirmed})
    };
    // 3. genesis
    if !b["genesis"].is_null() {
        let g = &b["genesis"];
        let empty = |x: &Value| x.as_array().map_or(false, |a| a.is_empty());
        if !empty(&b["inputs"]) || !empty(&h["inputs"]) {
            fail("genesis cannot consume inputs");
        }
        let supply = amount(&g["supply"]).unwrap_or_else(|| fail("malformed asset charter"));
        if !g.is_object() || !g["name"].is_string() {
            fail("malformed asset charter");
        }
        if outs.iter().any(|o| !matches!(s(o, "asset"), "" | "mint:")) {
            fail("genesis may only create its own asset");
        }
        if outs.iter().map(|o| amount(&o["amount"]).unwrap()).sum::<u128>() != supply {
            fail("genesis outputs must equal declared supply");
        }
        return statement(json!([]), Value::Null, json!([]));
    }
    // 4. spend
    let refs = b["inputs"].as_array().unwrap_or_else(|| fail("inputs"));
    let hin = h["inputs"].as_array().unwrap_or_else(|| fail("inputs"));
    let wins = w["inputs"].as_array().unwrap_or_else(|| fail("inputs"));
    if refs.is_empty() || refs.len() != hin.len() || refs.len() != wins.len() {
        fail("inputs do not match header");
    }
    let ids: BTreeSet<String> = refs.iter().map(|r| digest("parcel", r)).collect();
    if ids.len() != refs.len() {
        fail("duplicate input");
    }
    let sigils: BTreeSet<&str> = hin.iter().map(|x| x[0].as_str().unwrap_or("")).collect();
    if sigils.len() != hin.len() {
        fail("duplicate sigil");
    }
    let mut excluded: BTreeSet<String> = w["excluded"].as_array().map_or(BTreeSet::new(), |a| {
        a.iter().filter_map(Value::as_str).map(String::from).collect()
    });
    let mut relied: BTreeMap<(String, i64), Relied> = BTreeMap::new();
    let mut confirmed: BTreeMap<String, (i64, Value)> = BTreeMap::new();
    let rely = |relied: &mut BTreeMap<(String, i64), Relied>, cid: &str, v: i64, ch: &str, slack: i64| {
        let e = relied.entry((cid.to_string(), v)).or_insert(Relied { charter: ch.to_string(), slack });
        if e.charter != ch {
            fail("two different charters claimed for one version");
        }
        e.slack = e.slack.min(slack);
    };
    let confirm = |confirmed: &mut BTreeMap<String, (i64, Value)>, cid: &str, v: i64, ch: Value| {
        let e = confirmed.entry(cid.to_string()).or_insert((v, ch.clone()));
        if v < e.0 {
            *e = (v, ch);
        }
    };
    let children = &w["children"];
    let mut tin: BTreeMap<String, u128> = BTreeMap::new();
    let mut tout: BTreeMap<String, u128> = BTreeMap::new();
    for ((r, hi), iw) in refs.iter().zip(hin).zip(wins) {
        let ptx = s(r, "tx");
        let child = children.get(ptx).unwrap_or_else(|| fail("no proof for parent"));
        let p = &iw["parcel"];
        let i = r["i"].as_u64().unwrap_or(u64::MAX) as usize;
        let child_outs = child["outputs"].as_array().unwrap_or_else(|| fail("child outputs"));
        if !parcel_ok(p) || i >= child_outs.len() {
            fail("malformed input opening");
        }
        if Value::String(output_commitment(ptx, i, p)) != child_outs[i] {
            fail("input is not an output of its parent's proof");
        }
        let sg = hi[0].as_str().unwrap_or("");
        let gen = int(&hi[1]).unwrap_or(-1);
        if sigil_of(p) != sg {
            fail("header sigil does not match input parcel");
        }
        let seal = &iw["seal"];
        let home = s(p, "home");
        if seal["sigil"].as_str() != Some(sg) || seal["tid"].as_str() != Some(tid)
            || int(&seal["gen"]) != Some(gen) || seal["constellation"].as_str() != Some(home) {
            fail("seal does not match the input's sigil, home or generation");
        }
        let charter = &iw["charter"];
        let members: BTreeSet<&str> = charter["witnesses"].as_array().unwrap_or_else(|| fail("malformed charter"))
            .iter().filter_map(Value::as_str).collect();
        if members.is_empty() {
            fail("malformed charter");
        }
        let version = int(&charter["version"]).unwrap_or(-1);
        if version == 0 && digest("constellation", charter) != home {
            fail("charter version 0 does not match the constellation id");
        }
        let chash = digest("charter", charter);
        if int(&seal["version"]) != Some(version) {
            fail("seal does not name the supplied charter");
        }
        let mut counted: BTreeSet<&str> = BTreeSet::new();
        for v in seal["votes"].as_array().unwrap_or_else(|| fail("votes")) {
            let pk = v["witness"].as_str().unwrap_or("");
            if members.contains(pk) && !excluded.contains(pk) && !counted.contains(pk) {
                let full = json!({"constellation": home, "version": version, "witness": pk, "sigil": sg,
                                  "gen": gen, "tid": tid, "time": v["time"], "sig": v["sig"]});
                if vote_ok(&full) {
                    counted.insert(pk);
                }
            }
        }
        let q = quorum(members.len());
        if counted.len() < q {
            fail("seal lacks a quorum of valid votes");
        }
        rely(&mut relied, home, version, &chash, (counted.len() - q) as i64);
        let empty = json!({});
        if !evaluate(&p["lock"], unlocks.get(sg).unwrap_or(&empty), sg, tid) {
            fail("owner did not authorise this spend");
        }
        confirm(&mut confirmed, home, -1, Value::Null); // deep confirmation not modelled here
        *tin.entry(s(p, "asset").to_string()).or_default() += amount(&p["amount"]).unwrap();
    }
    // 5. conservation
    for o in outs {
        let a = s(o, "asset");
        if a.is_empty() || a == "mint:" {
            fail("asset placeholders are only valid in genesis");
        }
        *tout.entry(a.to_string()).or_default() += amount(&o["amount"]).unwrap();
    }
    let assets: BTreeSet<String> = tin.keys().chain(tout.keys()).cloned().collect();
    for a in assets {
        let x = a.strip_prefix("mint:").unwrap_or(&a).to_string();
        let m = format!("mint:{x}");
        let g = |t: &BTreeMap<String, u128>, k: &str| t.get(k).copied().unwrap_or(0);
        if g(&tin, &x) + g(&tin, &m) != g(&tout, &x) + g(&tout, &m) {
            fail("value not conserved");
        }
        if g(&tout, &m) > g(&tin, &m) {
            fail("mint right cannot grow");
        }
    }
    // Fold in the parents' statements (each distinct parent once).
    let parents: BTreeSet<&str> = refs.iter().map(|r| s(r, "tx")).collect();
    for ptx in parents {
        let c = &children[ptx];
        for row in c["relied"].as_array().unwrap() {
            rely(&mut relied, s(row, "cid"), int(&row["version"]).unwrap(), s(row, "charter"), int(&row["slack"]).unwrap());
        }
        for row in c["confirmed"].as_array().unwrap() {
            confirm(&mut confirmed, s(row, "cid"), int(&row["version"]).unwrap(), row["charter"].clone());
        }
        if let Some(ex) = c["excluded"].as_array() {
            let theirs: BTreeSet<String> = ex.iter().filter_map(Value::as_str).map(String::from).collect();
            excluded = excluded.intersection(&theirs).cloned().collect();
        }
    }
    let relied_v: Vec<Value> = relied.iter().map(|((cid, v), r)| json!({"cid": cid, "version": v, "charter": r.charter, "slack": r.slack})).collect();
    let confirmed_v: Vec<Value> = confirmed.iter().map(|(cid, (v, ch))| json!({"cid": cid, "version": v, "charter": ch})).collect();
    let excluded_v: Vec<Value> = excluded.into_iter().map(Value::String).collect();
    statement(Value::Array(relied_v), Value::Array(excluded_v), Value::Array(confirmed_v))
}

#[no_mangle]
pub extern "C" fn guest_main(ptr: *const u8, len: usize) -> u32 {
    unsafe { MARK = instret() };
    let input = unsafe { core::slice::from_raw_parts(ptr, len) };
    let w: Value = timed(0, || serde_json::from_slice(input).unwrap_or_else(|_| fail("witness is not JSON")));
    let st = timed(4, || step(&w));
    let d = digest("pcd-statement", &st);
    unsafe {
        let now = instret();
        SPENT[STACK[DEPTH]] += now - MARK;
        let mut line = format!("STATEMENT {d}\nPROFILE");
        for (i, c) in CATS.iter().enumerate() {
            line.push_str(&format!(" {c}={}", SPENT[i]));
        }
        line.push_str(&format!(" hashes={} hashed_bytes={} signatures={}\n", COUNTS[0], COUNTS[1], COUNTS[2]));
        print(&line);
    }
    0
}
