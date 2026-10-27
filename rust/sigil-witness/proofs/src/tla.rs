//! The TLA+ model (formal/Sigil.tla) restricted to one honest witness `w`.
//!
//! TLA+ state of `w` for one sigil `s`: `gen[w][s]` and `bound[w][s]`, plus `w`'s contribution
//! to the global `votes` set, `{<<ConsOf(w), w, s, g, t>>}`.
//!
//! **Abstraction function** α from the Rust witness to this state (per sigil `s`):
//!
//! ```text
//! α(rec).gen   = rec.gen
//! α(rec).bound = rec.tid            (None ↦ NoTid; "!contested" ↦ a phantom tid that no header has)
//! α(rec).votes = { <<v.constellation, v.witness, s, v.gen, v.tid>> : v ∈ rec.votes }
//! α(absent)    = (0, NoTid, {})
//! ```
//!
//! `rec.header`, `rec.vote`, `rec.abstain` and `rec.log` are not part of the TLA+ state.
//! All three components of α are exactly what STATUS (§5.3) returns, so α is computable from
//! the public interface of `Witness`.

/// A transition id in the abstract model (an index into a header table, or any id).
pub type Tid = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbsRec {
    pub gen: i128,
    pub bound: Option<Tid>,
}

impl AbsRec {
    pub const INIT: AbsRec = AbsRec { gen: 0, bound: None };
}

/// `Spend(w, s, t)` of Sigil.tla for the header generation `g = GenOf(t, s)`, with the
/// conjuncts `s ∈ SigilsOf(t)` and `Home[s] = ConsOf(w)` assumed (callers check them).
/// Returns the successor `(gen', bound')`; `votes' = votes ∪ {<<c, w, s, g, t>>}`.
pub fn spend(r: AbsRec, g: i128, t: Tid) -> Option<AbsRec> {
    let enabled = (g > r.gen && r.bound.is_none()) || (g == r.gen && (r.bound.is_none() || r.bound == Some(t)));
    if enabled {
        Some(AbsRec { gen: g, bound: Some(t) })
    } else {
        None
    }
}

/// `Release(w, s)` of Sigil.tla; `death_proof_exists` is `DeathProofExists(bound[w][s])`.
/// `votes` is unchanged.
pub fn release(r: AbsRec, death_proof_exists: bool) -> Option<AbsRec> {
    match r.bound {
        Some(_) if death_proof_exists => r.gen.checked_add(1).map(|gen| AbsRec { gen, bound: None }),
        _ => None,
    }
}
