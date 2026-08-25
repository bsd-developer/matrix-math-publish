//! Validated core domain types, canonical ordering, and hashing.
//!
//! This crate is the *functional core* of the platform (spec §17.2). It is
//! `no_std` + `alloc` on purpose: that structurally enforces the §4.3 restriction
//! that `mm-core` performs no I/O, reads no clock, and owns no ambient global
//! state. It also contains no floating-point arithmetic.
//!
//! Everything here establishes an invariant once, in a constructor, so that
//! downstream crates can rely on validated types instead of re-checking raw
//! integers (§5.3). Constructors reject rather than panic (§5.4).
//!
//! Module map to specification sections:
//!
//! | Module | Spec |
//! |---|---|
//! | [`codes`], [`error`] | §5.4 structured totality |
//! | [`level`], [`shape`], [`region`] | §5.1, §5.3, A.1 |
//! | [`dims`] | §0.2, §10.1 |
//! | [`modulus`] | §0.2, §6.6 |
//! | [`path`] | §5.2 node identity and canonical traversal |
//! | [`hash`], [`hex`] | §6.3 canonical digest |

#![no_std]
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

extern crate alloc;

pub mod codes;
pub mod dims;
pub mod error;
pub mod hash;
pub mod hex;
pub mod level;
pub mod modulus;
pub mod path;
pub mod region;
pub mod shape;

pub use codes::ErrorCode;
pub use dims::{Dim, MatMulInstance};
pub use error::{CoreError, CoreResult, Location};
pub use hash::{Sha256, sha256};
pub use hex::{decode_hex32, encode_hex};
pub use level::Level;
pub use modulus::PrimeModulus;
pub use path::{ChildStep, NodePath, RootStep, Step, TreeIndex};
pub use region::{Coordinate, Region};
pub use shape::Shape;

/// The specification version this build implements (§0.1).
///
/// A certificate whose `spec_version` differs is rejected rather than migrated
/// (§0.5): the project is permanently prelaunch and keeps no legacy readers.
pub const SPEC_VERSION: &str = "2.1.0";

/// The canonical certificate schema discriminator (§6.1).
pub const CERTIFICATE_SCHEMA: &str = "matrix-math-certificate/1";

/// The locked SHA-256 of source S1, `2608.16884v1.pdf` (§0.1).
///
/// Pinning the locked hashes in the checker binary is deliberate: §0.1 states
/// that the checked-in specification version *and its source hashes* identify
/// the semantics of every certificate. A certificate naming different sources is
/// rejected rather than reinterpreted.
pub const SOURCE_S1_SHA256: &str =
    "da7be6aadb5cb0611af8f033fb2984ab5a16f136230330371127d5877951c093";

/// The locked SHA-256 of source S2, `s41586-022-05172-4.pdf` (§0.1).
pub const SOURCE_S2_SHA256: &str =
    "42aea3994792b42358ca5d9d4c95cb3eac15f28254850a11d082b995aed8d401";
