//! End-to-end omega certificate evaluation (spec §6.5, §14.8).
//!
//! §14.8 requires a hand-computed `ℓ*=2` fixture. The fixture's free variables
//! are deliberately simple enough to check by inspection: uniform region
//! weights, uniform `α`, uniform `β`, and `μ = 1/4` at every positive level-2
//! node so that `H(μ,μ,1-2μ) = 3/2` exactly.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::ErrorCode;
use mm_exact::bridge::from_certificate;
use mm_exact::evaluate::evaluate;
use mm_rat::Rat;
use mm_schema::{CanonicalReader, Limits, decode_omega};
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

fn load(relative: &str) -> mm_schema::OmegaCertificate {
    let path = repo_root().join(relative);
    let file = fs::File::open(&path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::small());
    let certificate =
        decode_omega(&mut reader).unwrap_or_else(|error| panic!("decode {relative}: {error}"));
    reader.finish().expect("trailing bytes");
    certificate
}

#[test]
fn the_hand_fixture_decodes_with_the_expected_structure() {
    let certificate = load("tests/vectors/omega-l2-hand.json");
    assert_eq!(certificate.q, 5);
    assert_eq!(certificate.level.get(), 2);
    assert_eq!(certificate.log_precision_bits, 64);
    // §5.2: one root plus six regions of S_2, which has 15 shapes.
    assert_eq!(certificate.nodes.len(), 1 + 6 * 15);
    // §6.5: one block per occurrence of H_D^max, which at l*=2 is one per region.
    assert_eq!(certificate.blocks.len(), 6);
}

#[test]
fn the_hand_fixture_evaluates_and_satisfies_a21() {
    let certificate = load("tests/vectors/omega-l2-hand.json");
    let evaluable = from_certificate(&certificate).expect("bridge");
    let claim = evaluate(
        &evaluable.tree,
        &evaluable.blocks,
        &certificate.omega,
        evaluable.precision,
    )
    .expect("the hand fixture satisfies A21");
    assert_eq!(claim.omega, Rat::from_integer(1000));
    // The requirement is 2^(l*-1) * upper(log2(q+2)) = 2 * log2 7 ≈ 5.615.
    assert!(*claim.requirement.value() > Rat::from_signeds(56, 10));
    assert!(*claim.requirement.value() < Rat::from_signeds(57, 10));
    // M_total must be strictly positive, or omega would be unconstrained.
    assert!(claim.m_total.value().is_positive());
}

/// The optimizer-produced point, checked exactly.
///
/// This is the certificate behind the reported Track A result, so a regression
/// here is a regression in the claim itself. The bound is asserted as an
/// interval rather than an exact rational: the value is a property of the
/// optimizer run, and pinning it would make an improved run look like a failure.
#[test]
fn the_optimized_fixture_evaluates_and_satisfies_a21() {
    let certificate = load("tests/vectors/omega-l2-optimized.json");
    assert_eq!(certificate.q, 5);
    assert_eq!(certificate.level.get(), 2);
    let evaluable = from_certificate(&certificate).expect("bridge");
    let claim = evaluate(
        &evaluable.tree,
        &evaluable.blocks,
        &certificate.omega,
        evaluable.precision,
    )
    .expect("the optimized fixture satisfies A21");
    // omega <= 2.3749, which is what the reported result claims.
    assert!(claim.omega < Rat::from_signeds(23749, 10000));
    assert!(claim.omega > Rat::from_integer(2));
    assert!(claim.m_total.value().is_positive());
    // A21 with no slack to spare: the producer chose the least accepted omega.
    let left = claim.e_total.value() + &(claim.m_total.value() * &claim.omega);
    assert!(left >= *claim.requirement.value());
}

/// The `ℓ* = 3` path, end to end on a real certificate.
///
/// This is the fixture that exercises A.5's concatenation recursion and A12–A15,
/// none of which a level-2 instance reaches at all. It is a *uniform* point, so
/// the bound it carries is poor; what it certifies is that the interior
/// machinery runs and agrees, not that the number is good.
///
/// Ignored by default: the evaluation takes about a minute, which belongs in the
/// slow tier rather than the per-change one (§12.8).
#[test]
#[ignore = "about a minute; runs under `just test-slow`"]
fn the_level_three_fixture_evaluates_and_satisfies_a21() {
    let certificate = load("tests/vectors/omega-l3-uniform.json");
    assert_eq!(certificate.level.get(), 3);
    let evaluable = from_certificate(&certificate).expect("bridge");
    assert_eq!(evaluable.blocks.len(), 762);
    let claim = evaluate(
        &evaluable.tree,
        &evaluable.blocks,
        &certificate.omega,
        evaluable.precision,
    )
    .expect("the level-three fixture satisfies A21");
    // The requirement is 2^(l*-1) * upper(log2(q+2)) = 4 * log2 7 ≈ 11.229.
    assert!(*claim.requirement.value() > Rat::from_signeds(112, 10));
    assert!(*claim.requirement.value() < Rat::from_signeds(113, 10));
    assert!(claim.m_total.value().is_positive());
    // The interior levels contribute; a level-2 instance has none.
    let bounds = mm_exact::evaluate::evaluate_bounds(
        &evaluable.tree,
        &evaluable.blocks,
        evaluable.precision,
    )
    .expect("bounds");
    assert!(bounds.e_interior.value().is_positive());
}

#[test]
fn an_infeasible_omega_is_rejected() {
    let certificate = load("schemas/fixtures/invalid/omega_feasibility_violated.json");
    let evaluable = from_certificate(&certificate).expect("bridge");
    let error = evaluate(
        &evaluable.tree,
        &evaluable.blocks,
        &certificate.omega,
        evaluable.precision,
    )
    .expect_err("omega = 0 cannot satisfy A21 here");
    assert_eq!(error.code(), ErrorCode::FeasibilityViolated);
    assert_eq!(error.equation_id(), Some("A21"));
}

/// §7.2: a negative omega is rejected at decode time, before any evaluation.
#[test]
fn a_negative_omega_is_rejected_at_decode() {
    let path = repo_root().join("schemas/fixtures/invalid/omega_negative.json");
    let file = fs::File::open(&path).expect("open");
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::small());
    let error = decode_omega(&mut reader).expect_err("negative omega");
    assert_eq!(error.code(), ErrorCode::NegativeOmega);
    assert_eq!(error.equation_id(), Some("§7.2"));
}

/// §6.5: `log_precision_bits` must lie in `[32, 4096]`.
#[test]
fn an_out_of_range_precision_is_rejected() {
    let path = repo_root().join("schemas/fixtures/invalid/omega_bad_precision.json");
    let file = fs::File::open(&path).expect("open");
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::small());
    let error = decode_omega(&mut reader).expect_err("precision 8 is out of range");
    assert_eq!(error.code(), ErrorCode::UnsupportedInstance);
}

/// A decomposition certificate must not decode as an omega certificate.
#[test]
fn the_wrong_certificate_kind_is_rejected() {
    let path = repo_root().join("tests/vectors/strassen-z.json");
    let file = fs::File::open(&path).expect("open");
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::small());
    let error = decode_omega(&mut reader).expect_err("kind mismatch");
    assert!(
        matches!(
            error.code(),
            ErrorCode::SchemaMismatch | ErrorCode::UnknownField
        ),
        "unexpected code {}",
        error.code()
    );
}
