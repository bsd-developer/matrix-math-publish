//! `expand` is meaning-preserving (`docs/specs/0007_spec.md` §4, §6).
//!
//! The decisive property: for a symmetric certificate, converting to groups and
//! expanding back reproduces the original **byte for byte**. That is stronger
//! than checking the two agree structurally, because canonical bytes are the
//! artifact identity of §6.3 and what a published result is retrieved by.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::ErrorCode;
use mm_schema::symmetric::{decode_symmetric_omega, encode_symmetric_omega, expand, to_symmetric};
use mm_schema::{CanonicalReader, Limits, decode_omega, encode_omega};
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

fn load(relative: &str) -> (mm_schema::OmegaCertificate, Vec<u8>) {
    let path = repo_root().join(relative);
    let bytes = fs::read(&path).unwrap_or_else(|error| panic!("read {path:?}: {error}"));
    let file = fs::File::open(&path).expect("open");
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::default());
    let certificate = decode_omega(&mut reader).expect("decode");
    reader.finish().expect("trailing bytes");
    (certificate, bytes)
}

fn reencode(certificate: &mm_schema::OmegaCertificate) -> Vec<u8> {
    let mut out = Vec::new();
    encode_omega(&mut out, certificate).expect("encode");
    out
}

#[test]
fn a_symmetric_certificate_round_trips_byte_for_byte() {
    // §2: both l*=3 vectors are symmetric, verified by comparing the decoded
    // free variables of every group and every region.
    for relative in [
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l3-uniform.json",
    ] {
        let (general, _) = load(relative);
        let original = reencode(&general);

        let symmetric = to_symmetric(&general).expect("l*=3 vectors are symmetric");
        // §3.5: 60 groups and 22 blocks at l*=3, against 5,779 nodes and 762.
        assert_eq!(symmetric.groups.len(), 60, "{relative}");
        assert_eq!(symmetric.blocks.len(), 22, "{relative}");
        assert_eq!(general.nodes.len(), 5_779, "{relative}");
        assert_eq!(general.blocks.len(), 762, "{relative}");

        let expanded = expand(&symmetric).expect("expand");
        assert_eq!(
            reencode(&expanded),
            original,
            "{relative}: expand(to_symmetric(c)) must reproduce c byte for byte"
        );
    }
}

#[test]
fn an_asymmetric_certificate_is_rejected_rather_than_projected() {
    // §2 records that the published l*=2 point is not symmetric: its root alpha
    // differs across regions and twelve of its fifteen groups differ across
    // their six copies. Averaging or picking a representative would change the
    // mathematical object, so the converter decides membership instead.
    let (general, _) = load("tests/vectors/omega-l2-optimized.json");
    let error = to_symmetric(&general).expect_err("the published l*=2 point is asymmetric");
    assert_eq!(error.code(), ErrorCode::SymmetryViolated);
}

#[test]
fn the_hand_fixture_is_symmetric_and_shrinks() {
    // §3.5: 451 general rationals at l*=2 against 81 symmetric, a 5.6x cut.
    let (general, _) = load("tests/vectors/omega-l2-hand.json");
    let symmetric = to_symmetric(&general).expect("the hand fixture is symmetric");
    assert_eq!(symmetric.groups.len(), 15);
    assert_eq!(symmetric.blocks.len(), 1);
    assert_eq!(general.nodes.len(), 91);
    assert_eq!(general.blocks.len(), 6);
    assert_eq!(
        reencode(&expand(&symmetric).expect("expand")),
        reencode(&general)
    );
}

#[test]
fn the_symmetric_encoding_survives_a_full_byte_round_trip() {
    // The whole path: general bytes -> groups -> canonical symmetric bytes ->
    // decode -> expand -> general bytes. Byte equality at both ends.
    for relative in [
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l2-hand.json",
    ] {
        let (general, _) = load(relative);
        let original = reencode(&general);

        let symmetric = to_symmetric(&general).expect("symmetric");
        let mut bytes = Vec::new();
        let (_digest, count) = encode_symmetric_omega(&mut bytes, &symmetric).expect("encode");
        assert_eq!(count as usize, bytes.len(), "{relative}: byte count");

        let mut reader =
            CanonicalReader::new(std::io::Cursor::new(bytes.clone()), Limits::default());
        let decoded = decode_symmetric_omega(&mut reader).expect("decode");
        reader.finish().expect("trailing bytes");

        assert_eq!(
            reencode(&expand(&decoded).expect("expand")),
            original,
            "{relative}"
        );

        // The point of the encoding: the symmetric bytes are far smaller.
        assert!(
            bytes.len() * 4 < original.len(),
            "{relative}: symmetric {} bytes vs general {}",
            bytes.len(),
            original.len()
        );
        println!(
            "  {relative}: general {} bytes -> symmetric {} bytes ({:.1}x)",
            original.len(),
            bytes.len(),
            original.len() as f64 / bytes.len() as f64
        );
    }
}
