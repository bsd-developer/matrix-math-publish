//! Deterministic flip-graph search over decompositions (spec §10.5–§10.8).
//!
//! Search is **untrusted** (§1.1): it may be approximate, nondeterministic,
//! incomplete, or wrong. Its only job is to produce a candidate whose exact
//! certificate the Lean checker can accept. What it must be is *replayable*:
//! §12.3 R2 requires that the same config and seed reach the same witness at the
//! same worker step.

#![forbid(unsafe_code)]
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::todo,
    clippy::unimplemented,
    missing_docs,
    rust_2018_idioms
)]

pub mod bridge;
pub mod f2;
pub mod rng;
pub mod walk;
pub mod witness;

pub use bridge::{decomposition_to_state, state_to_decomposition};
pub use f2::{F2State, F2Term, F2Vec};
pub use rng::{ChaCha20Rng, Seed256, derive_worker_seed};
pub use walk::{RestartPolicy, Walk, WalkConfig, WalkOutcome, WalkSnapshot};
pub use witness::Witness;
