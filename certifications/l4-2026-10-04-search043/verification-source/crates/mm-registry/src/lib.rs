//! Content-addressed storage, manifests, and run records (spec §13).
//!
//! This is single-machine persistence and the I/O shell for artifacts. It is
//! untrusted: nothing here can change a checker verdict (§17.7).

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

pub mod cas;
pub mod tcb;

pub use cas::Cas;
pub use tcb::TcbLedger;
