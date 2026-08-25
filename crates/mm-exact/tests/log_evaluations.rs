//! Directed logarithm evaluation counts (`docs/specs/0004_spec.md` §2.2, §4.1).
//!
//! P5 selects a precision from the number of directed logarithm evaluations one
//! check performs. That number has to be a count rather than an estimate from
//! the node count, because an estimate silently stops tracking the instance the
//! moment `ℓ*` or the tree shape changes.
//!
//! `mm_rat::log2` carries a process-global evaluation counter. It is diagnostic
//! — read, never branched on, and no checker verdict can depend on it — but a
//! process-global counter cannot be measured from two threads at once. These
//! assertions therefore live in their own test binary, serialized on one lock,
//! rather than in `omega_fixtures.rs` alongside tests that also evaluate
//! logarithms. `0004_spec.md` §7.1 names that file; putting the counter tests
//! anywhere with concurrent siblings would make them flaky, which is worse than
//! the deviation.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_exact::bridge::from_certificate;
use mm_exact::evaluate::evaluate_bounds;
use mm_schema::{CanonicalReader, Limits, decode_omega};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

/// Serializes every test in this binary; the counter is process-global.
static COUNTER: Mutex<()> = Mutex::new(());

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn load(relative: &str) -> mm_schema::OmegaCertificate {
    let path = repo_root().join(relative);
    let file = fs::File::open(&path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::small());
    let certificate =
        decode_omega(&mut reader).unwrap_or_else(|error| panic!("decode {relative}: {error}"));
    reader.finish().expect("trailing bytes");
    certificate
}

/// P2: what a checker performs, derived from what `evaluate_bounds` performs.
///
/// The Rust evaluator computes both endpoints of the §7.4 closeness test from
/// one enclosure where the Lean checker calls `log2Lower` and `log2Upper`
/// separately, so the Lean checker performs one extra evaluation per block
/// domain point. And `evaluate_bounds` stops before A21, which encloses
/// `log2(q+2)` once more. This is the same arithmetic `mm omega-min` reports as
/// `log_evaluations`.
fn checker_evaluations(relative: &str) -> u64 {
    let _guard = COUNTER.lock().unwrap_or_else(|error| error.into_inner());
    let certificate = load(relative);
    let evaluable = from_certificate(&certificate).expect("bridge");
    mm_rat::log2::reset_evaluations();
    evaluate_bounds(&evaluable.tree, &evaluable.blocks, evaluable.precision).expect("evaluate");
    let domain_points: u64 = evaluable.blocks.iter().map(|b| b.y.len() as u64).sum();
    mm_rat::log2::evaluations() + domain_points + 1
}

#[test]
fn the_l2_certificate_costs_the_appendix_a_evaluation_count() {
    assert_eq!(
        checker_evaluations("tests/vectors/omega-l2-optimized.json"),
        1_028
    );
}

#[test]
#[ignore = "slow tier: the exact ℓ*=3 evaluation costs minutes; `just test-slow` runs it"]
fn the_l3_certificate_costs_the_appendix_a_evaluation_count() {
    assert_eq!(
        checker_evaluations("tests/vectors/omega-l3-optimized.json"),
        83_012
    );
    // The uniform certificate has the same tree, the same 762 blocks, and the
    // same 5,778 domain points, so it produces the identical count. The count is
    // a function of the instance shape and of which entries are zero; it does
    // not depend on the precision.
    assert_eq!(
        checker_evaluations("tests/vectors/omega-l3-uniform.json"),
        83_012
    );
}

/// The symmetric path's P2 count, which nothing pinned before.
///
/// `0004_spec.md` §4.1 makes this figure a MUST: it has to bound the Lean
/// checker, because P5 derives the declared precision from it. Two mechanisms
/// feed it and they must agree about how often a checker visits a group.
///
/// `GroupInvariants` hoists the region-invariant entropies and charges back the
/// six evaluations a checker performs, so the counter describes a per-region
/// walk. The §7.4 correction — one extra evaluation per block domain point,
/// because Lean calls `log2Lower` and `log2Upper` separately — must therefore
/// also be per-region. In the general encoding a group's block already appears
/// once per region, so summing `y.len()` counts them all; in the symmetric
/// encoding `blocks` holds one entry per group, so the same sum counts each
/// once and needs the region factor.
///
/// Without it the reported count was 13,544 where 14,534 bounds the checker —
/// the two halves of one expression disagreeing, which is exactly what a test
/// on the whole expression catches and a test on either half does not.
#[test]
#[ignore = "slow tier: the exact ℓ*=3 evaluation costs minutes; `just test-slow` runs it"]
fn the_symmetric_count_is_per_region() {
    use mm_schema::symmetric::to_symmetric;
    let general = load("tests/vectors/omega-l3-optimized.json");
    let certificate = to_symmetric(&general).expect("the l*=3 vector is symmetric");

    let domain_points: usize = certificate.blocks.iter().map(|block| block.y.len()).sum();
    assert_eq!(certificate.blocks.len(), 22, "one block per group at l*=3");
    assert_eq!(
        domain_points, 198,
        "block domain points, counted once per group"
    );

    let precision =
        mm_rat::log2::Precision::new(certificate.log_precision_bits).expect("precision");
    let _guard = COUNTER
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    mm_rat::log2::reset_evaluations();
    mm_exact::symmetric::group_evaluate_bounds(&certificate, precision).expect("evaluate");
    let counted = mm_rat::log2::evaluations();

    let regions = 6;
    let reported = counted + (regions * domain_points as u64) + 1;
    assert_eq!(counted, 13_345, "charged evaluations at l*=3");
    assert_eq!(
        reported, 14_534,
        "the P2 figure a symmetric checker is bounded by"
    );
    assert!(
        reported > counted + domain_points as u64 + 1,
        "the correction must be per region, not per group"
    );
}
