//! `mm cas-put` and `mm cas-get` (spec §9.2, §13.6).
//!
//! The CAS stores immutable blobs addressed by the SHA-256 of their
//! **uncompressed canonical** content. `cas-put` canonicalizes before storing,
//! so a certificate that is not already canonical is rejected rather than
//! silently stored under a digest nobody else would compute. `cas-get` verifies
//! the digest after retrieval (§13.6).

use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_registry::Cas;
use mm_schema::encode_decomposition;
use std::fs;
use std::path::PathBuf;

fn store() -> CoreResult<Cas> {
    Cas::open(PathBuf::from("data/cas"))
}

/// Run `mm cas-put`.
///
/// # Errors
///
/// Propagates decode, canonicalization, and I/O failures.
pub fn put(arguments: &[String]) -> CoreResult<u8> {
    let path = arguments
        .iter()
        .find(|argument| !argument.starts_with("--"))
        .map(PathBuf::from)
        .ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "mm cas-put needs a file"))?;

    // Decode first: storing bytes we cannot decode would put an unusable blob
    // under a content address (§13.6).
    let (certificate, _) = crate::verify::load(&path)?;
    let mut canonical = Vec::new();
    let (digest, byte_count) = encode_decomposition(&mut canonical, &certificate.decomposition)?;
    if digest != certificate.digest {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "canonicalization changed the certificate identity",
        )
        .equation("§6.3"));
    }
    let stored = store()?.put(&canonical)?;
    println!("{stored}");
    eprintln!("cas-put: stored {byte_count} canonical bytes");
    Ok(0)
}

/// Run `mm cas-get`.
///
/// # Errors
///
/// Returns [`ErrorCode::DigestMismatch`] when stored bytes do not hash to their
/// name, and [`ErrorCode::Io`] when the blob is absent.
pub fn get(arguments: &[String]) -> CoreResult<u8> {
    let mut digest: Option<String> = None;
    let mut out: Option<PathBuf> = None;
    let mut index = 0usize;
    while let Some(argument) = arguments.get(index) {
        match argument.as_str() {
            "--out" => {
                out = arguments.get(index + 1).map(PathBuf::from);
                index += 1;
            }
            other if other.starts_with("--") => {
                return Err(CoreError::new(ErrorCode::BadConfig, "unknown flag").value(other));
            }
            other => digest = Some(other.to_owned()),
        }
        index += 1;
    }
    let digest =
        digest.ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "mm cas-get needs a digest"))?;
    // Validate the digest shape before touching the filesystem.
    let _ = mm_core::hex::decode_hex32(&digest)?;
    let data = store()?.get(&digest)?;
    match out {
        Some(path) => {
            fs::write(&path, &data).map_err(|error| {
                CoreError::new(ErrorCode::Io, format!("write {path:?}: {error}"))
            })?;
            eprintln!("cas-get: wrote {} bytes to {}", data.len(), path.display());
        }
        None => {
            use std::io::Write;
            std::io::stdout()
                .write_all(&data)
                .map_err(|error| CoreError::new(ErrorCode::Io, error.to_string()))?;
        }
    }
    Ok(0)
}
