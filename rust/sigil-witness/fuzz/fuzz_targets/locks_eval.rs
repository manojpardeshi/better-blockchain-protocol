//! Lock evaluation: no panic; batch and single verification agree; the lock language is
//! monotone in time (eval at a clock implies eval with time ignored, which `Witness::spend`
//! relies on); eval implies well formed; and agreement with an independent spec oracle.
#![no_main]
use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use sigil_witness::locks::{evaluate, keys_in, well_formed};
use sigil_witness_proofs::fuzzgen::{LockCase, LockCtx, LOCK_SIGIL, LOCK_TID};
use sigil_witness_proofs::world::{default_headers, World};

static CTX: OnceLock<LockCtx> = OnceLock::new();

fuzz_target!(|case: LockCase| {
    let ctx = CTX.get_or_init(|| LockCtx::new(&World::new(&default_headers())));
    let lock = ctx.lock_json(&case.lock, 0);
    let unlock = ctx.unlock_json(&case.unlock, LOCK_SIGIL, LOCK_TID);
    let now = case.now.map(|t| t as i128);
    let r = evaluate(&lock, &unlock, LOCK_SIGIL, LOCK_TID, now, false);
    let rb = evaluate(&lock, &unlock, LOCK_SIGIL, LOCK_TID, now, true);
    assert_eq!(r, rb, "batch verification changed a lock verdict");
    let wf = well_formed(&lock);
    if r {
        assert!(wf, "an ill-formed lock evaluated to true");
        assert!(evaluate(&lock, &unlock, LOCK_SIGIL, LOCK_TID, None, false), "lock not monotone in time");
    }
    if let Some(e) = ctx.expected_wf(&case.lock) {
        assert_eq!(e, wf, "well_formed differs from the spec oracle: {}", lock.canonical_string());
    }
    if let Some(e) = ctx.expected(&case.lock, &case.unlock, now) {
        assert_eq!(e, r, "evaluate differs from the spec oracle: {} / {}", lock.canonical_string(), unlock.canonical_string());
    }
    let _ = keys_in(&lock);
});
