//! `to_symmetric` must compare every block, not a prefix of them.
//!
//! The converter decided R1's third clause — that all blocks attached to one
//! group are equal — by walking `block_count` slots six at a time. That is
//! 22 × 6 = 132 entries at `ℓ*=3` against the 762 the general encoding carries,
//! and 762 of 207,906 at `ℓ*=4`. Everything past the bound, which is every node
//! in regions two through six, went unread, and the converter kept region one's
//! block as the representative — the "select a representative" §6 forbids.
//!
//! `ℓ*=2` cannot catch this: `block_count(2) == 1`, so one slot times six
//! regions covers all six blocks exactly. These tests are at `ℓ*=3` for that
//! reason, and they tamper a block in the *upper* range specifically.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::codes::ErrorCode;
use mm_rat::rational::Rat;
use mm_schema::symmetric::to_symmetric;
use mm_schema::{CanonicalReader, Limits, OmegaCertificate, decode_omega};
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

fn load(relative: &str) -> OmegaCertificate {
    let path = repo_root().join(relative);
    let file = fs::File::open(&path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::default());
    let certificate = decode_omega(&mut reader).expect("decode");
    reader.finish().expect("trailing bytes");
    certificate
}

/// Region one's blocks occupy the first slot of each group's six. A block past
/// the old 132-entry bound belongs to a later region, which is exactly the range
/// that went unexamined.
#[test]
fn a_block_past_the_old_bound_is_compared() {
    let mut certificate = load("tests/vectors/omega-l3-optimized.json");
    assert!(
        certificate.blocks.len() > 132,
        "the l*=3 instance must carry more blocks than the old bound examined"
    );
    certificate.blocks[200].epsilon = Rat::from_signeds(1, 7);
    let error =
        to_symmetric(&certificate).expect_err("a differing block has no symmetric encoding");
    assert_eq!(error.code(), ErrorCode::SymmetryViolated);
}

/// The last block of all is the strongest case: nothing after it can mask a
/// missing comparison.
#[test]
fn the_final_block_is_compared() {
    let mut certificate = load("tests/vectors/omega-l3-optimized.json");
    let last = certificate.blocks.len() - 1;
    certificate.blocks[last].epsilon = Rat::from_signeds(1, 7);
    let error = to_symmetric(&certificate).expect_err("the last block is still a block");
    assert_eq!(error.code(), ErrorCode::SymmetryViolated);
}

/// Every block, so a future bound that is short by any amount fails here rather
/// than silently selecting a representative.
#[test]
fn every_block_is_compared() {
    let clean = load("tests/vectors/omega-l3-optimized.json");
    to_symmetric(&clean).expect("the untampered certificate converts");
    for index in 0..clean.blocks.len() {
        let mut certificate = clean.clone();
        certificate.blocks[index].epsilon = Rat::from_signeds(1, 7);
        match to_symmetric(&certificate) {
            Ok(_) => panic!("block {index} was tampered and the conversion still succeeded"),
            Err(error) => assert_eq!(
                error.code(),
                ErrorCode::SymmetryViolated,
                "block {index} was compared but rejected for the wrong reason"
            ),
        }
    }
}
