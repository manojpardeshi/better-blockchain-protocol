//! Machine-checked assurance for the Rust Sigil witness (see docs/VERIFY_RUST.md).
//!
//! * [`tla`]: the TLA+ model (formal/Sigil.tla) for one witness, and the abstraction function;
//! * [`model_rust`]: a transcription of the witness's record logic, which the Kani proofs in
//!   `kani_proofs` are about;
//! * [`world`], [`checker`]: a real `Witness` in a fixed world, with every step checked
//!   against the TLA+ step, the transcription and the safety invariants. Used by the bounded
//!   exhaustive checker (tests/refinement_bfs.rs), the fuzz targets and the differential test.

pub mod checker;
#[cfg(feature = "fuzz")]
pub mod fuzzgen;
pub mod model_rust;
pub mod tla;
pub mod world;

#[cfg(kani)]
mod kani_proofs;
