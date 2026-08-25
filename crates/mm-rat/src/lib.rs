//! Exact rationals, directed bounds, and diagnostic transcendental enclosures.
//!
//! This crate is `no_std` + `alloc`, which structurally enforces the §4.3
//! restriction that `mm-rat` performs no I/O. It contains no floating-point
//! arithmetic on the authoritative path.
//!
//! The central design rule is §7.1: **direction is visible in the type**. A
//! single ambiguous `log2` or `entropy` method is forbidden in the checker,
//! because the final Track A inequality is only sound when every term was
//! rounded in the conservative direction (§7.2).

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

pub mod bounds;
pub mod entropy;
pub mod grammar;
pub mod log2;
pub mod rational;

pub use bounds::{Interval, LowerBound, UpperBound};
pub use grammar::MAX_INTEGER_DIGITS;
pub use rational::Rat;
