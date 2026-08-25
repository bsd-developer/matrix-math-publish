//! Exact rings, matrix-multiplication tensors, decompositions, and basis maps.
//!
//! This crate is the Track B mathematical core (spec §10, Appendix B). It is
//! `no_std` + `alloc` and contains no floating-point arithmetic (§4.3).

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

pub mod basis;
pub mod decomposition;
pub mod iso;
pub mod moves;
pub mod ring;
pub mod verify;

pub use decomposition::{Decomposition, Term};
pub use ring::{
    ExactRing, Gaussian, GaussianRationalRing, IntegerRing, PrimeField, RationalRing, RingTag,
};
pub use verify::{DecompositionClaim, target_entry, target_support, verify_decomposition};
