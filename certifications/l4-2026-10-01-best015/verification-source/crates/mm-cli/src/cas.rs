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
use mm_schema::{DecompositionCertificate, Limits, OmegaCertificate, encode_decomposition};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};

/// The supported decoded forms behind one canonical published artifact.
pub(crate) enum Certificate {
    Decomposition(DecompositionCertificate),
    Omega(OmegaCertificate),
    Symmetric(mm_schema::symmetric::SymmetricCertificate),
}

impl Certificate {
    pub(crate) const fn kind(&self) -> &'static str {
        match self {
            Self::Decomposition(_) => "decomposition",
            Self::Omega(_) | Self::Symmetric(_) => "omega",
        }
    }

    pub(crate) const fn encoding(&self) -> Option<&'static str> {
        match self {
            Self::Decomposition(_) => None,
            Self::Omega(_) => Some("general"),
            Self::Symmetric(_) => Some("symmetric"),
        }
    }
}

/// Typed input bound to the exact, uncompressed canonical bytes.
pub(crate) struct CanonicalInput {
    pub(crate) certificate: Certificate,
    pub(crate) bytes: Vec<u8>,
    pub(crate) digest: String,
}

fn published_form(published: &crate::verify::PublishedBytes) -> CoreResult<&'static str> {
    // The rational claim can exceed a fixed-size header. Read canonical fields
    // rather than searching a truncated prefix for an encoding marker.
    let mut reader =
        mm_schema::CanonicalReader::new(BufReader::new(published.reader()?), Limits::default());
    reader.begin_object()?;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "kind" => match reader.read_string()?.as_str() {
                "decomposition" => return Ok("decomposition"),
                "omega" => {}
                _ => {
                    return Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "unsupported certificate kind",
                    ));
                }
            },
            "payload" => {
                reader.begin_object()?;
                if reader.next_key()?.as_deref() != Some("encoding") {
                    return Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "omega payload needs an encoding",
                    ));
                }
                return match reader.read_string()?.as_str() {
                    "general" => Ok("omega"),
                    "symmetric" => Ok("symmetric"),
                    _ => Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "unsupported omega encoding",
                    )),
                };
            }
            _ => reader.skip_value()?,
        }
    }
    Err(CoreError::new(
        ErrorCode::SchemaMismatch,
        "certificate kind is missing",
    ))
}

/// Decode and round-trip every supported form before storing or reporting it.
pub(crate) fn load_canonical(path: &Path) -> CoreResult<CanonicalInput> {
    let published = crate::verify::open_published(path, Limits::default())?;
    let (certificate, expected) = match published_form(&published)? {
        "decomposition" => {
            let certificate = mm_schema::load_decomposition_certificate(
                BufReader::new(published.reader()?),
                Limits::default(),
            )?;
            let digest = certificate.digest_hex();
            (Certificate::Decomposition(certificate), digest)
        }
        "symmetric" => {
            let (certificate, digest) = crate::verify::decode_published_symmetric(&published)?;
            (Certificate::Symmetric(certificate), digest)
        }
        "omega" => {
            let (certificate, digest) = crate::verify::decode_published_omega(&published)?;
            (Certificate::Omega(certificate), digest)
        }
        _ => {
            return Err(CoreError::new(
                ErrorCode::SchemaMismatch,
                "unsupported certificate kind",
            ));
        }
    };
    let mut compare = crate::roundtrip::CompareWriter::new(published.reader()?);
    let (digest, count) = match &certificate {
        Certificate::Decomposition(value) => {
            encode_decomposition(&mut compare, &value.decomposition)?
        }
        Certificate::Omega(value) => mm_schema::encode_omega(&mut compare, value)?,
        Certificate::Symmetric(value) => {
            mm_schema::symmetric::encode_symmetric_omega(&mut compare, value)?
        }
    };
    compare.finish()?;
    let bytes = published.to_vec()?;
    if mm_core::hex::encode_hex(&digest) != expected
        || mm_core::sha256(&bytes) != digest
        || bytes.len() as u64 != count
    {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "canonical bytes changed between decoding, round trip and storage",
        )
        .equation("§3.5"));
    }
    Ok(CanonicalInput {
        certificate,
        bytes,
        digest: expected,
    })
}

/// Store only the validated canonical content under its checked digest.
pub(crate) fn store_canonical(store: &Cas, input: &CanonicalInput) -> CoreResult<String> {
    if mm_core::hex::encode_hex(&mm_core::sha256(&input.bytes)) != input.digest {
        return Err(CoreError::new(
            ErrorCode::DigestMismatch,
            "canonical artifact identity changed",
        ));
    }
    store.put(&input.bytes)
}

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

    let input = load_canonical(&path)?;
    let stored = store_canonical(&store()?, &input)?;
    println!("{stored}");
    eprintln!("cas-put: stored {} canonical bytes", input.bytes.len());
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

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly"
    )]
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct Temporary(PathBuf);
    impl Temporary {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "mm-canonical-cas-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).expect("fresh test directory");
            Self(path)
        }
    }
    impl Drop for Temporary {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn fixture(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/vectors")
            .join(name)
    }

    fn examples(directory: &Path) -> Vec<PathBuf> {
        let general = load_canonical(&fixture("omega-l2-hand.json")).expect("general fixture");
        let Certificate::Omega(certificate) = general.certificate else {
            panic!("omega fixture")
        };
        let symmetric =
            mm_schema::symmetric::to_symmetric(&certificate).expect("symmetric fixture");
        let path = directory.join("symmetric.json");
        let file = fs::File::create(&path).expect("create symmetric file");
        mm_schema::symmetric::encode_symmetric_omega(file, &symmetric).expect("encode symmetric");
        vec![
            fixture("naive-1x1x1-z.json"),
            fixture("omega-l2-hand.json"),
            path,
        ]
    }

    #[test]
    fn all_supported_forms_store_their_exact_canonical_identity() {
        let temp = Temporary::new();
        let store = Cas::open(temp.0.join("cas")).expect("CAS");
        for (path, expected) in examples(&temp.0).into_iter().zip([
            ("decomposition", None),
            ("omega", Some("general")),
            ("omega", Some("symmetric")),
        ]) {
            let input = load_canonical(&path).expect("canonical input");
            assert_eq!(
                (input.certificate.kind(), input.certificate.encoding()),
                expected
            );
            let digest = store_canonical(&store, &input).expect("store");
            assert_eq!(digest, input.digest);
            assert_eq!(
                store.get(&digest).expect("retrieve"),
                fs::read(path).expect("fixture bytes")
            );
        }
    }

    #[test]
    fn compressed_transport_stores_uncompressed_bytes_for_every_form() {
        let temp = Temporary::new();
        let store = Cas::open(temp.0.join("cas")).expect("CAS");
        for (index, path) in examples(&temp.0).into_iter().enumerate() {
            let compressed = std::process::Command::new("zstd")
                .args(["-q", "-c"])
                .arg(&path)
                .output()
                .expect("locked zstd transport");
            assert!(compressed.status.success());
            let transport = temp.0.join(format!("transport-{index}.json.zst"));
            fs::write(&transport, &compressed.stdout).expect("compressed fixture");
            let plain = load_canonical(&path).expect("plain");
            let restored = load_canonical(&transport).expect("compressed input");
            assert_eq!(plain.digest, restored.digest);
            assert_eq!(plain.bytes, restored.bytes);
            assert_ne!(
                mm_core::hex::encode_hex(&mm_core::sha256(&compressed.stdout)),
                plain.digest
            );
            assert_eq!(
                store_canonical(&store, &restored).expect("store"),
                plain.digest
            );
            assert_eq!(store.get(&plain.digest).expect("retrieve"), plain.bytes);
        }
    }

    #[test]
    fn changed_content_cannot_be_stored_under_the_decoded_identity() {
        let temp = Temporary::new();
        let store = Cas::open(temp.0.join("cas")).expect("CAS");
        let mut input = load_canonical(&fixture("naive-1x1x1-z.json")).expect("fixture");
        input.bytes.push(b' ');
        assert_eq!(
            store_canonical(&store, &input)
                .expect_err("mutation")
                .code(),
            ErrorCode::DigestMismatch
        );
        assert!(!store.contains(&input.digest));
    }

    #[test]
    fn malformed_or_unknown_input_is_rejected_before_storage() {
        let temp = Temporary::new();
        for (index, bytes) in [
            b"{\"kind\":\"unsupported\"}".as_slice(),
            b"{\"kind\":\"omega\"}",
            b"{ \"kind\":\"decomposition\"}",
        ]
        .into_iter()
        .enumerate()
        {
            let path = temp.0.join(format!("invalid-{index}.json"));
            fs::write(&path, bytes).expect("fixture");
            assert!(load_canonical(&path).is_err());
        }
    }

    #[test]
    fn an_exact_claim_larger_than_a_header_does_not_break_encoding_dispatch() {
        let temp = Temporary::new();
        let input = load_canonical(&fixture("omega-l2-hand.json")).expect("fixture");
        let Certificate::Omega(mut certificate) = input.certificate else {
            panic!("omega fixture")
        };
        certificate.omega = mm_rat::Rat::from_ratio(
            format!("1{}", "0".repeat(4095))
                .parse()
                .expect("large integer"),
            malachite::Integer::from(1),
        )
        .expect("exact large claim");
        let symmetric = mm_schema::symmetric::to_symmetric(&certificate).expect("symmetric");
        let mut general = Vec::new();
        mm_schema::encode_omega(&mut general, &certificate).expect("encode general");
        let mut compact = Vec::new();
        mm_schema::symmetric::encode_symmetric_omega(&mut compact, &symmetric)
            .expect("encode symmetric");
        for (index, (bytes, encoding)) in [(general, "general"), (compact, "symmetric")]
            .into_iter()
            .enumerate()
        {
            let path = temp.0.join(format!("large-{index}.json"));
            fs::write(&path, &bytes).expect("write fixture");
            let restored = load_canonical(&path).expect("supported encoding beyond fixed header");
            assert_eq!(restored.certificate.encoding(), Some(encoding));
            assert_eq!(restored.bytes, bytes);
        }
    }
}
