//! A line-by-line transcription of the record logic of `Witness::spend_inner` and
//! `Witness::release_inner` (rust/sigil-witness/src/witness.rs) over abstract values.
//!
//! Everything that is not record logic is collapsed into booleans: `authorised` is "the
//! request passed the home check and `authorises(..)` returned `Some((g, t))` at our clock",
//! `expired` is `now > unlock.expires`, `proof_ok` is `proves_dead(..)`. Votes are abstracted
//! to their `(gen, tid)`; every vote this witness signs carries its own constellation, key and
//! the request's sigil, so those are fixed per record.
//!
//! The logic never reads `rec.votes` (it only appends), so it is written over [`Core`], the
//! fields it reads, plus "the vote appended". The Kani harnesses in `kani_proofs.rs` prove
//! properties of `spend_core` / `release_core`; the bounded exhaustive checker
//! (`tests/refinement_bfs.rs`) and the fuzz target `witness_ops` check at run time that the real
//! witness behaves exactly as `spend` / `release` (the same functions on whole records) predict,
//! which is what ties the proofs to the shipped code.

use crate::tla::{AbsRec, Tid};

/// `CONTESTED` ("!contested"), which only a store written by a future ADOPT can contain.
pub const CONTESTED: Tid = Tid::MAX;

/// `authorises` accepts generations `0 <= g < 2^62`.
pub const GEN_LIMIT: i128 = 1 << 62;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct RustRec {
    pub gen: i128,
    pub tid: Option<Tid>,
    /// `rec.vote`, as the `(gen, tid)` of the stored vote.
    pub vote: Option<(i128, Tid)>,
    pub abstain: bool,
    /// `rec.votes`, as `(gen, tid)` pairs, oldest first.
    pub votes: Vec<(i128, Tid)>,
}

/// The fields of a record the logic reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Core {
    pub gen: i128,
    pub tid: Option<Tid>,
    pub vote: Option<(i128, Tid)>,
    pub abstain: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpendOut {
    /// `Ok(vote)`, the returned vote's `(gen, tid)`.
    Vote((i128, Tid)),
    /// `Err(Conflict(vote))`.
    Conflict(Option<(i128, Tid)>),
    /// `Err(Rejected(_))` or `Err(BadRequest(_))`.
    Rejected,
}

impl RustRec {
    pub fn alpha(&self) -> AbsRec {
        AbsRec { gen: self.gen, bound: self.tid }
    }

    pub fn core(&self) -> Core {
        Core { gen: self.gen, tid: self.tid, vote: self.vote, abstain: self.abstain }
    }
}

/// `spend_inner` from the record lookup on. `existing` is `st.records.get(sigil)`. Returns the
/// reply, the record's fields afterwards (`None`: no record stored) and the vote appended to
/// `rec.votes`, if any.
pub fn spend_core(
    existing: Option<Core>,
    authorised: bool,
    expired: bool,
    gen: i128,
    tid: Tid,
) -> (SpendOut, Option<Core>, Option<(i128, Tid)>) {
    if !authorised {
        return (SpendOut::Rejected, existing, None);
    }
    // Fast path.
    if let Some(r) = existing {
        if gen == r.gen {
            match (r.tid, r.vote) {
                (Some(t), _) if t != tid => return (SpendOut::Conflict(r.vote), existing, None),
                (Some(_), Some(v)) => return (SpendOut::Vote(v), existing, None),
                _ => {}
            }
        }
    }
    let mut rec = existing.unwrap_or_default();
    if gen < rec.gen {
        return (SpendOut::Rejected, existing, None);
    }
    if gen > rec.gen {
        if rec.tid.is_some() {
            return (SpendOut::Rejected, existing, None);
        }
        rec.gen = gen;
    }
    if rec.tid.is_none() {
        if expired {
            return (SpendOut::Rejected, existing, None);
        }
        rec.tid = Some(tid);
    }
    if rec.tid != Some(tid) {
        return (SpendOut::Conflict(rec.vote), existing, None);
    }
    if rec.vote.is_none() && rec.abstain {
        return (SpendOut::Rejected, existing, None);
    }
    let mut pushed = None;
    if rec.vote.is_none() {
        // `fresh` is signed over (sigil, gen, tid, now) of the request.
        rec.vote = Some((gen, tid));
        pushed = Some((gen, tid));
    }
    match rec.vote {
        Some(v) => (SpendOut::Vote(v), Some(rec), pushed),
        None => unreachable!("vote set"),
    }
}

/// `spend_core` on a whole record.
pub fn spend(
    existing: Option<&RustRec>,
    authorised: bool,
    expired: bool,
    gen: i128,
    tid: Tid,
) -> (SpendOut, Option<RustRec>) {
    let (out, core, pushed) = spend_core(existing.map(RustRec::core), authorised, expired, gen, tid);
    let rec = core.map(|c| {
        let mut votes = existing.map(|r| r.votes.clone()).unwrap_or_default();
        votes.extend(pushed);
        RustRec { gen: c.gen, tid: c.tid, vote: c.vote, abstain: c.abstain, votes }
    });
    (out, rec)
}

/// `release_inner` from the frozen check on. Returns `Ok(new gen)` or `Err(())` (rejected),
/// and the fields afterwards; `votes` is unchanged.
pub fn release_core(existing: Option<Core>, frozen: bool, proof_ok: bool) -> (Result<i128, ()>, Option<Core>) {
    if frozen {
        return (Err(()), existing);
    }
    let r = match existing {
        Some(r) if r.tid.is_some() && r.tid != Some(CONTESTED) => r,
        _ => return (Err(()), existing),
    };
    if !proof_ok {
        return (Err(()), existing);
    }
    let mut rec = r;
    rec.gen += 1;
    rec.tid = None;
    rec.vote = None;
    rec.abstain = false;
    (Ok(rec.gen), Some(rec))
}

/// `release_core` on a whole record.
pub fn release(existing: Option<&RustRec>, frozen: bool, proof_ok: bool) -> (Result<i128, ()>, Option<RustRec>) {
    let (out, core) = release_core(existing.map(RustRec::core), frozen, proof_ok);
    let rec = core.map(|c| RustRec {
        gen: c.gen,
        tid: c.tid,
        vote: c.vote,
        abstain: c.abstain,
        votes: existing.map(|r| r.votes.clone()).unwrap_or_default(),
    });
    (out, rec)
}
