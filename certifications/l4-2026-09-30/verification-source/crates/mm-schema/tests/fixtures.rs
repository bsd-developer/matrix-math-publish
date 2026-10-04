//! Curated fixture conformance (spec §6.7, §12.4, §12.7, Appendix B).
//!
//! These tests are the independent Rust side of the differential contract
//! (§12.6): the fixtures are produced by untrusted Python, and nothing about
//! them is believed until this checker re-derives every value from the canonical
//! bytes.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::ErrorCode;
use mm_schema::{Limits, encode_decomposition, load_decomposition_certificate};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn load(path: &Path) -> mm_schema::DecompositionCertificate {
    let file = fs::File::open(path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
    load_decomposition_certificate(BufReader::new(file), Limits::small())
        .unwrap_or_else(|error| panic!("decode {path:?}: {error}"))
}

fn fixture_paths(directory: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("read_dir {directory:?}: {error}"))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "json")
        })
        .collect();
    paths.sort();
    paths
}

/// Whether a fixture declares the decomposition certificate kind (§6.1).
///
/// The corpus holds both kinds. A decomposition test that swept an omega
/// certificate would be measuring the kind check rather than what it claims to.
fn is_decomposition(path: &Path) -> bool {
    fs::read_to_string(path)
        .map(|text| text.contains("\"kind\":\"decomposition\""))
        .unwrap_or(false)
}

fn decomposition_fixtures(directory: &Path) -> Vec<PathBuf> {
    fixture_paths(directory)
        .into_iter()
        .filter(|path| is_decomposition(path))
        .collect()
}

/// Every curated positive fixture must decode and reconstruct its tensor exactly.
#[test]
fn every_curated_fixture_verifies() {
    let root = repo_root();
    let mut checked = 0;
    for directory in [
        root.join("tests/vectors"),
        root.join("schemas/fixtures/valid"),
    ] {
        for path in decomposition_fixtures(&directory) {
            let certificate = load(&path);
            let claim = certificate
                .decomposition
                .verify()
                .unwrap_or_else(|error| panic!("verify {path:?}: {error}"));
            assert_eq!(
                claim.term_count,
                certificate.decomposition.term_count(),
                "{path:?}"
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 20,
        "expected the full curated corpus, saw {checked}"
    );
}

/// §12.4 known-answer tests, by exact term count and instance.
#[test]
fn known_answer_term_counts() {
    let root = repo_root();
    let cases: [(&str, u16, u16, u16, usize); 12] = [
        ("tests/vectors/strassen-z.json", 2, 2, 2, 7),
        ("tests/vectors/strassen-f2.json", 2, 2, 2, 7),
        ("tests/vectors/naive-1x1x1-z.json", 1, 1, 1, 1),
        ("tests/vectors/naive-2x2x2-z.json", 2, 2, 2, 8),
        ("tests/vectors/naive-3x3x3-z.json", 3, 3, 3, 27),
        ("tests/vectors/naive-4x4x4-z.json", 4, 4, 4, 64),
        ("tests/vectors/naive-5x5x5-z.json", 5, 5, 5, 125),
        ("tests/vectors/naive-2x3x4-z.json", 2, 3, 4, 24),
        ("tests/vectors/alphatensor-f2-2x2x2.json", 2, 2, 2, 7),
        ("tests/vectors/alphatensor-f2-3x3x3.json", 3, 3, 3, 23),
        ("tests/vectors/alphatensor-f2-4x4x4.json", 4, 4, 4, 47),
        ("tests/vectors/alphatensor-z-3x3x3.json", 3, 3, 3, 23),
    ];
    for (relative, n, m, p, term_count) in cases {
        let path = root.join(relative);
        let certificate = load(&path);
        let instance = certificate.decomposition.instance();
        assert_eq!(instance.n().get(), n, "{relative} n");
        assert_eq!(instance.m().get(), m, "{relative} m");
        assert_eq!(instance.p().get(), p, "{relative} p");
        assert_eq!(
            certificate.decomposition.term_count(),
            term_count,
            "{relative}"
        );
        certificate
            .decomposition
            .verify()
            .unwrap_or_else(|error| panic!("{relative}: {error}"));
    }
}

/// The headline Track B witness: AlphaTensor's 47-term `T_4` over `F2`.
///
/// Accepting it proves `rank_{F2}(T_4) <= 47` and **nothing stronger** (§10.4).
#[test]
fn alphatensor_t4_f2_proves_rank_at_most_47() {
    let path = repo_root().join("tests/vectors/alphatensor-f2-4x4x4.json");
    let certificate = load(&path);
    let claim = certificate.decomposition.verify().expect("reconstructs T4");
    assert_eq!(claim.term_count, 47);
    assert_eq!(claim.statement(), "rank(T[4,4,4]) <= 47");
}

/// §6.3: canonical encoding is idempotent byte-for-byte, and the digest of the
/// re-encoded bytes equals the digest of the original file.
#[test]
fn canonical_encoding_round_trips_byte_for_byte() {
    let root = repo_root();
    for directory in [
        root.join("tests/vectors"),
        root.join("schemas/fixtures/valid"),
    ] {
        for path in decomposition_fixtures(&directory) {
            let original = fs::read(&path).expect("read fixture");
            let certificate = load(&path);
            let mut re_encoded = Vec::new();
            let (digest, byte_count) =
                encode_decomposition(&mut re_encoded, &certificate.decomposition)
                    .unwrap_or_else(|error| panic!("encode {path:?}: {error}"));
            assert_eq!(
                re_encoded, original,
                "{path:?} did not round-trip byte-for-byte"
            );
            assert_eq!(digest, certificate.digest, "{path:?} digest");
            assert_eq!(byte_count, certificate.byte_count, "{path:?} byte count");
            assert_eq!(byte_count as usize, original.len(), "{path:?} length");
        }
    }
}

/// §6.8: the certificate digest must agree with an independent SHA-256.
#[test]
fn digest_agrees_with_an_independent_sha256() {
    let root = repo_root();
    let path = root.join("tests/vectors/alphatensor-f2-4x4x4.json");
    let bytes = fs::read(&path).expect("read fixture");
    let certificate = load(&path);
    // Independent recomputation over the whole buffer, rather than the
    // incremental digest the streaming reader accumulated.
    assert_eq!(mm_core::sha256(&bytes), certificate.digest);

    let output = std::process::Command::new("shasum")
        .arg("-a")
        .arg("256")
        .arg(&path)
        .output();
    if let Ok(output) = output
        && output.status.success()
    {
        let text = String::from_utf8_lossy(&output.stdout);
        let system_digest = text.split_whitespace().next().unwrap_or_default();
        assert_eq!(
            system_digest,
            certificate.digest_hex(),
            "system shasum disagrees for {path:?}"
        );
    }
}

/// §6.7 and §12.7: every invalid fixture class rejects with its stable code.
#[test]
fn every_invalid_fixture_rejects_with_its_stable_code() {
    let root = repo_root();
    let expected: [(&str, ErrorCode); 19] = [
        ("bad_rational_grammar", ErrorCode::BadRationalGrammar),
        ("composite_modulus", ErrorCode::CompositeModulus),
        ("count_mismatch", ErrorCode::CountMismatch),
        ("duplicated_term", ErrorCode::ReconstructionMismatch),
        ("noncanonical_json", ErrorCode::NoncanonicalJson),
        ("noncanonical_json_whitespace", ErrorCode::NoncanonicalJson),
        ("noncanonical_term_order", ErrorCode::NoncanonicalTermOrder),
        ("reconstruction_mismatch", ErrorCode::ReconstructionMismatch),
        ("removed_term", ErrorCode::ReconstructionMismatch),
        ("schema_mismatch", ErrorCode::SchemaMismatch),
        ("source_hash_mismatch", ErrorCode::SourceHashMismatch),
        ("spec_version_mismatch", ErrorCode::SpecVersionMismatch),
        ("transposed_output", ErrorCode::ReconstructionMismatch),
        ("truncated", ErrorCode::InvalidJson),
        ("unknown_field", ErrorCode::UnknownField),
        ("unsupported_instance", ErrorCode::UnsupportedInstance),
        ("wrong_field", ErrorCode::BadRationalGrammar),
        ("wrong_vector_length", ErrorCode::WrongVectorLength),
        ("zero_factor", ErrorCode::ZeroFactor),
    ];
    for (name, code) in expected {
        let path = root
            .join("schemas/fixtures/invalid")
            .join(format!("{name}.json"));
        let file = fs::File::open(&path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
        let outcome = load_decomposition_certificate(BufReader::new(file), Limits::small())
            .and_then(|certificate| certificate.decomposition.verify().map(|_| ()));
        let error = outcome.expect_err(&format!("{name} must be rejected"));
        assert_eq!(error.code(), code, "{name}: {error}");
    }
}

/// Rejections must be deterministic: the same bytes always yield the same code
/// and the same first-failure location (§5.4).
#[test]
fn rejections_are_deterministic() {
    let root = repo_root();
    for path in fixture_paths(&root.join("schemas/fixtures/invalid")) {
        // Omega certificates are a different kind; the decomposition decoder
        // rejects them for kind reasons, which is not what this test measures.
        if path
            .file_name()
            .is_some_and(|name| name.to_string_lossy().starts_with("omega_"))
        {
            continue;
        }
        let mut seen: Option<String> = None;
        for _ in 0..3 {
            let file = fs::File::open(&path).expect("open");
            let outcome = load_decomposition_certificate(BufReader::new(file), Limits::small())
                .and_then(|certificate| certificate.decomposition.verify().map(|_| ()));
            let rendered = outcome
                .err()
                .map(|error| error.to_canonical_json())
                .unwrap_or_default();
            match &seen {
                None => seen = Some(rendered),
                Some(previous) => assert_eq!(previous, &rendered, "{path:?} is nondeterministic"),
            }
        }
    }
}
