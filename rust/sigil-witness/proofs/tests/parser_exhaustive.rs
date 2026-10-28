//! Exhaustive bounded panic-freedom checks of the REAL `json::parse` (Kani could not finish
//! these: symbolic bytes through `from_utf8`, map and number code ran out of memory or time).
//!
//! The alphabet has JSON punctuation, escapes, digits, literal starts, whitespace and the bytes
//! of multi-byte UTF-8 characters (é = c3 a9, € = e2 82 ac) plus a stray continuation byte.

use std::panic;

const ALPHABET: [u8; 20] = [
    b'"', b'\\', b'u', b'0', b'1', b'a', b'[', b']', b'{', b'}', b':', b',', b'-', b'n', b' ', b'.', 0xc3, 0xa9, 0xe2, 0x82,
];

fn panics(input: &[u8]) -> bool {
    panic::catch_unwind(|| {
        if let Ok(v) = sigil_witness::json::parse(input) {
            let c = v.canonical();
            assert_eq!(sigil_witness::json::parse(&c).map(|w| w.canonical()), Ok(c));
        }
    })
    .is_err()
}

fn for_all(prefix: &[u8], n: usize, f: &mut dyn FnMut(&[u8])) {
    let mut buf = prefix.to_vec();
    fn go(buf: &mut Vec<u8>, left: usize, f: &mut dyn FnMut(&[u8])) {
        f(buf);
        if left == 0 {
            return;
        }
        for &b in &ALPHABET {
            buf.push(b);
            go(buf, left - 1, f);
            buf.pop();
        }
    }
    go(&mut buf, n, f);
}

/// Every input of up to 5 bytes over the alphabet: no panic, and canonical output round-trips.
#[test]
fn parse_never_panics_on_short_inputs() {
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let mut n = 0u64;
    let mut bad = Vec::new();
    for_all(b"", 5, &mut |s| {
        n += 1;
        if panics(s) {
            bad.push(s.to_vec());
        }
    });
    panic::set_hook(hook);
    eprintln!("RESULT: {n} inputs of <= 5 bytes, {} panics", bad.len());
    assert!(bad.is_empty(), "panics on {:?}", &bad[..bad.len().min(5)]);
}

/// Every `"\u` followed by up to 5 alphabet bytes. Failed before the bug 1 fix
/// (e.g. `"\u11` + `é` ...).
#[test]
fn parse_never_panics_after_unicode_escape() {
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let mut n = 0u64;
    let mut bad = Vec::new();
    for_all(b"\"\\u", 5, &mut |s| {
        n += 1;
        if panics(s) {
            bad.push(String::from_utf8_lossy(s).into_owned());
        }
    });
    panic::set_hook(hook);
    eprintln!("RESULT: {n} inputs, {} panics, e.g. {:?}", bad.len(), &bad[..bad.len().min(3)]);
    assert!(bad.is_empty(), "{} of {n} inputs panic", bad.len());
}
