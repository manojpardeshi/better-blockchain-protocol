//! `json::parse` never panics; canonical output is ASCII, re-parses to the same value, and is
//! a fixpoint.
#![no_main]
use libfuzzer_sys::fuzz_target;
use sigil_witness::json::parse;

fuzz_target!(|data: &[u8]| {
    if cfg!(feature = "skip_known_bugs") && sigil_witness_proofs::fuzzgen::hits_known_parser_panic(data) {
        return;
    }
    if let Ok(v) = parse(data) {
        let c = v.canonical();
        assert!(c.is_ascii(), "canonical output is not ASCII");
        let v2 = parse(&c).expect("canonical output must parse");
        assert_eq!(v2, v, "canonical output parses to another value");
        assert_eq!(v2.canonical(), c, "canonical encoding is not a fixpoint");
    }
});
