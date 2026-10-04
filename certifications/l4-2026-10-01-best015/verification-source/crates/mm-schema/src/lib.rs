//! Versioned certificate model, canonical encoding, and bounded decoding.
//!
//! Canonical bytes are UTF-8 JSON conforming to RFC 8785 plus the stricter rules
//! of §6.2 and §6.3, and the certificate identity is the SHA-256 of those
//! uncompressed bytes (§6.3). Zstandard is transport compression only.

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

pub mod certificate;
pub mod limits;
pub mod omega;
pub mod reader;
pub mod symmetric;
pub mod writer;

pub use certificate::{
    AnyDecomposition, CertificateKind, DecompositionCertificate, decode_decomposition,
    encode_decomposition,
};
pub use limits::{Limits, Meter};
pub use omega::{BlockPayload, NodePayload, OmegaCertificate, decode_omega, encode_omega};
pub use reader::CanonicalReader;
pub use writer::CanonicalWriter;

use mm_core::error::CoreResult;
use std::io::BufRead;

/// Decode a decomposition certificate and return it with its canonical identity.
///
/// # Errors
///
/// Propagates the first structured rejection (§5.4).
pub fn load_decomposition_certificate<R: BufRead>(
    input: R,
    limits: Limits,
) -> CoreResult<DecompositionCertificate> {
    let mut reader = CanonicalReader::new(input, limits);
    let decomposition = decode_decomposition(&mut reader)?;
    let byte_count = reader.offset();
    let digest = reader.finish()?;
    Ok(DecompositionCertificate {
        decomposition,
        digest,
        byte_count,
    })
}
