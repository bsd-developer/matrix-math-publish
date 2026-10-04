//! Independent exact Track A evaluator (spec §4.3, §14.8).
//!
//! This crate is a **diagnostic cross-check** and is never the sole authority
//! (§1.1, §3.1). It is written independently of the Lean checker on purpose:
//! §4.1 chooses independence over DRY so that a mistake in one implementation is
//! caught by the other rather than duplicated.
//!
//! Nothing here may depend on the optimizer or the search (§17.7).

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
pub mod domain;
pub mod evaluate;
pub mod instance;
pub mod maxent;
pub mod symmetric;
pub mod tree;

pub use bridge::{EvaluableOmega, from_certificate};
pub use domain::{ShapeDomain, SupportVector, support_vectors};
pub use instance::OmegaInstance;
pub use tree::{NodeVariables, TrackATree};
