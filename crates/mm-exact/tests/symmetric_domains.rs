//! The symmetric evaluator must reject exactly what the general one rejects.
//!
//! `0007_spec.md` §5.1 relates the two checkers by an *equality*, not an
//! implication, so a certificate the general path refuses must not be evaluated
//! here either. The gap these tests pin was real: with no A.2 validation on the
//! group path, a root whose six region weights were each `1` — summing to six —
//! was accepted and reported `omega_min = 0`, while the general path returned
//! `bad_simplex`. A checker that accepts `ω ≤ 0` is not a lenient checker.
//!
//! `ℓ*=2` is the level used here on purpose. It is the level the original
//! negative fixture covered, and it still failed to catch this, because the
//! fixture rejects on the free-variable clause before any domain is examined.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::codes::ErrorCode;
use mm_exact::symmetric::group_evaluate_bounds;
use mm_rat::log2::Precision;
use mm_rat::rational::Rat;
use mm_schema::symmetric::{GroupPayload, SymmetricCertificate, to_symmetric};
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

fn symmetric_hand() -> SymmetricCertificate {
    let path = repo_root().join("tests/vectors/omega-l2-hand.json");
    let file = fs::File::open(&path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::default());
    let general = decode_omega(&mut reader).expect("decode");
    reader.finish().expect("trailing bytes");
    to_symmetric(&general).expect("the hand certificate is symmetric")
}

fn precision(certificate: &SymmetricCertificate) -> Precision {
    Precision::new(certificate.log_precision_bits).expect("declared precision")
}

/// The untampered certificate still evaluates, so a rejection below is the
/// tamper and not the new validation pass refusing everything.
#[test]
fn the_clean_certificate_is_still_accepted() {
    let certificate = symmetric_hand();
    let precision = precision(&certificate);
    group_evaluate_bounds(&certificate, precision).expect("a valid certificate must evaluate");
}

#[test]
fn root_region_weights_that_do_not_sum_to_one_are_refused() {
    let mut certificate = symmetric_hand();
    let GroupPayload::Branching { region_weights, .. } = &mut certificate.root else {
        panic!("the root is branching");
    };
    for weight in region_weights.iter_mut() {
        *weight = Rat::one();
    }
    let precision = precision(&certificate);
    let error = group_evaluate_bounds(&certificate, precision)
        .expect_err("six weights of one sum to six, not one");
    assert_eq!(error.code(), ErrorCode::BadSimplex);
}

#[test]
fn root_region_weights_of_the_wrong_length_are_refused() {
    let mut certificate = symmetric_hand();
    let GroupPayload::Branching { region_weights, .. } = &mut certificate.root else {
        panic!("the root is branching");
    };
    region_weights.truncate(2);
    let precision = precision(&certificate);
    let error = group_evaluate_bounds(&certificate, precision)
        .expect_err("A_T must carry one weight per region");
    assert_eq!(error.code(), ErrorCode::CountMismatch);
}

/// A truncated `A_T` used to be absorbed by `.get(r).unwrap_or(zero)`, which
/// silently weighted the missing regions zero *and* dropped the §7.4 evaluation
/// count that `0004_spec.md` P5 derives the declared precision from. Length is
/// checked before any of that reads it.
#[test]
fn a_group_distribution_of_the_wrong_length_is_refused() {
    let mut certificate = symmetric_hand();
    let mut touched = false;
    for payload in &mut certificate.groups {
        if let GroupPayload::ZeroShape { beta } = payload
            && beta.len() > 1
        {
            beta.truncate(1);
            touched = true;
            break;
        }
    }
    assert!(
        touched,
        "the l*=2 instance has a zero-shape group to tamper"
    );
    let precision = precision(&certificate);
    let error = group_evaluate_bounds(&certificate, precision)
        .expect_err("beta must cover its support domain");
    assert_eq!(error.code(), ErrorCode::CountMismatch);
}

#[test]
fn a_group_distribution_that_does_not_sum_to_one_is_refused() {
    let mut certificate = symmetric_hand();
    let mut touched = false;
    for payload in &mut certificate.groups {
        if let GroupPayload::ZeroShape { beta } = payload
            && let Some(first) = beta.first_mut()
        {
            *first = mm_rat::rational::sum([&first.clone(), &Rat::one()]);
            touched = true;
            break;
        }
    }
    assert!(
        touched,
        "the l*=2 instance has a zero-shape group to tamper"
    );
    let precision = precision(&certificate);
    let error = group_evaluate_bounds(&certificate, precision)
        .expect_err("adding one to an entry breaks the simplex");
    assert_eq!(error.code(), ErrorCode::BadSimplex);
}

/// §3.3 requires the variant to be checked against the kind the position
/// implies. It was not, and consumers absorbed the mismatch instead: a
/// non-branching positive group at level ≥ 3 hit a `continue` and contributed
/// zero to `E_ℓ`, where the general evaluator returns `bad_path`.
#[test]
fn a_payload_that_disagrees_with_its_position_is_refused() {
    let mut certificate = symmetric_hand();
    let index = certificate
        .groups
        .iter()
        .position(|payload| matches!(payload, GroupPayload::LevelTwo { .. }))
        .expect("the l*=2 instance has a level-two group");
    certificate.groups[index] = GroupPayload::ZeroShape {
        beta: vec![Rat::one()],
    };
    let precision = precision(&certificate);
    let error = group_evaluate_bounds(&certificate, precision)
        .expect_err("a level-two position must carry a level-two payload");
    assert_eq!(error.code(), ErrorCode::BadPath);
}

/// `μ` outside `[0, 1/2]` was caught only incidentally, as `bad_simplex` raised
/// from inside `term_enclosure` at §7.3, rather than at §3.3 naming the group.
#[test]
fn a_level_two_mu_outside_its_interval_is_refused() {
    let mut certificate = symmetric_hand();
    let mut touched = false;
    for payload in &mut certificate.groups {
        if let GroupPayload::LevelTwo { mu } = payload {
            *mu = Rat::from_signeds(3, 4);
            touched = true;
            break;
        }
    }
    assert!(touched, "the l*=2 instance has a level-two group");
    let precision = precision(&certificate);
    let error = group_evaluate_bounds(&certificate, precision)
        .expect_err("3/4 is outside the A.2 interval [0, 1/2]");
    assert_eq!(error.code(), ErrorCode::BadSimplex);
}
