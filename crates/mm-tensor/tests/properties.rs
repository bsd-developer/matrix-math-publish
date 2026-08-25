//! Mandatory metamorphic properties for Track B (spec §12.5, §10.4–§10.7,
//! Appendix B.2–B.6).

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use malachite::Integer;
use mm_core::dims::{MatMulInstance, TensorMode};
use mm_core::modulus::PrimeModulus;
use mm_tensor::basis::{Matrix, map_factors};
use mm_tensor::decomposition::{Decomposition, Term, normalize_term};
use mm_tensor::iso::{cyclic_shift, transpose};
use mm_tensor::moves::{flip, other_modes, plus, reduce};
use mm_tensor::ring::{ExactRing, IntegerRing, PrimeField, RationalRing};
use mm_tensor::{target_entry, target_support, verify_decomposition};

fn instance(n: u16, m: u16, p: u16) -> MatMulInstance {
    MatMulInstance::from_raw(n, m, p).expect("supported instance")
}

/// The naive `nmp`-term decomposition, used as a known-good starting point.
fn naive<R: ExactRing>(target: MatMulInstance, ring: R) -> Decomposition<R> {
    let len_a = target.mode_len(TensorMode::A).expect("ok");
    let len_b = target.mode_len(TensorMode::B).expect("ok");
    let len_c = target.mode_len(TensorMode::C).expect("ok");
    let mut terms = Vec::new();
    for i in 0..target.n().as_usize() {
        for k in 0..target.m().as_usize() {
            for j in 0..target.p().as_usize() {
                let mut u = vec![ring.zero(); len_a];
                let mut v = vec![ring.zero(); len_b];
                let mut w = vec![ring.zero(); len_c];
                u[target.flat_a(i, k).expect("ok")] = ring.one();
                v[target.flat_b(k, j).expect("ok")] = ring.one();
                w[target.flat_c_dual(j, i).expect("ok")] = ring.one();
                terms.push(Term::new(u, v, w));
            }
        }
    }
    Decomposition::new(target, ring, terms).expect("valid naive decomposition")
}

/// The exact tensor sum of a term list, as a sorted sparse coordinate list.
fn tensor_sum<R: ExactRing>(
    ring: &R,
    target: MatMulInstance,
    terms: &[Term<R::Elem>],
) -> Vec<(usize, usize, usize, String)> {
    let len_a = target.mode_len(TensorMode::A).expect("ok");
    let len_b = target.mode_len(TensorMode::B).expect("ok");
    let len_c = target.mode_len(TensorMode::C).expect("ok");
    let mut out = Vec::new();
    for a in 0..len_a {
        for b in 0..len_b {
            for c in 0..len_c {
                let mut total = ring.zero();
                for term in terms {
                    let product = ring.mul(&term.u[a], &term.v[b]);
                    if ring.is_zero(&product) {
                        continue;
                    }
                    total = ring.add(&total, &ring.mul(&product, &term.w[c]));
                }
                if !ring.is_zero(&total) {
                    out.push((a, b, c, ring.encode(&total)));
                }
            }
        }
    }
    out
}

#[test]
fn target_support_matches_the_entrywise_definition() {
    for (n, m, p) in [(1u16, 1u16, 1u16), (2, 2, 2), (2, 3, 4), (3, 2, 3)] {
        let target = instance(n, m, p);
        let support: std::collections::BTreeSet<_> = target_support(target)
            .expect("support")
            .into_iter()
            .collect();
        assert_eq!(
            support.len(),
            usize::from(n) * usize::from(m) * usize::from(p),
            "T[{n},{m},{p}] support size"
        );
        let len_a = target.mode_len(TensorMode::A).expect("ok");
        let len_b = target.mode_len(TensorMode::B).expect("ok");
        let len_c = target.mode_len(TensorMode::C).expect("ok");
        for a in 0..len_a {
            for b in 0..len_b {
                for c in 0..len_c {
                    let expected = support.contains(&(a, b, c));
                    assert_eq!(
                        target_entry(target, a, b, c).expect("in range"),
                        expected,
                        "T[{n},{m},{p}][{a},{b},{c}]"
                    );
                }
            }
        }
    }
}

/// §12.5: cyclic tensor mode permutation preserves reconstruction.
#[test]
fn cyclic_shift_preserves_reconstruction() {
    for (n, m, p) in [(2u16, 2u16, 2u16), (2, 3, 4), (1, 2, 3)] {
        let decomposition = naive(instance(n, m, p), IntegerRing);
        let shifted = cyclic_shift(&decomposition).expect("shift");
        let claim = verify_decomposition(&shifted).expect("cyclic image reconstructs");
        assert_eq!(claim.term_count, decomposition.term_count());
        assert_eq!(claim.instance, instance(m, p, n));
        // Three shifts return to the original instance.
        let back = cyclic_shift(&cyclic_shift(&shifted).expect("shift")).expect("shift");
        assert_eq!(back.instance(), decomposition.instance());
        verify_decomposition(&back).expect("round trip reconstructs");
    }
}

/// §12.5: the transpose isomorphism preserves reconstruction.
#[test]
fn transpose_preserves_reconstruction() {
    for (n, m, p) in [(2u16, 2u16, 2u16), (2, 3, 4), (3, 1, 2)] {
        let decomposition = naive(instance(n, m, p), IntegerRing);
        let transposed = transpose(&decomposition).expect("transpose");
        let claim = verify_decomposition(&transposed).expect("transpose reconstructs");
        assert_eq!(claim.instance, instance(p, m, n));
        assert_eq!(claim.term_count, decomposition.term_count());
        // The transpose is an involution.
        let back = transpose(&transposed).expect("transpose");
        assert_eq!(back.instance(), decomposition.instance());
        for (left, right) in back.terms().iter().zip(decomposition.terms()) {
            assert_eq!(left, right, "transpose is not involutive");
        }
    }
}

/// §12.5: basis change followed by its inverse maps a decomposition back exactly.
#[test]
fn basis_change_round_trips_exactly() {
    let ring = PrimeField::new(PrimeModulus::new(7).expect("prime"));
    let target = instance(2, 2, 2);
    let decomposition = naive(target, ring);

    // Independently chosen invertible matrices over F7.
    let a = Matrix::new(4, 4, vec![1, 2, 0, 0, 0, 1, 0, 0, 3, 0, 1, 0, 0, 0, 4, 1]).expect("shape");
    let b = Matrix::new(4, 4, vec![2, 0, 0, 1, 0, 1, 5, 0, 0, 0, 3, 0, 1, 0, 0, 1]).expect("shape");
    let c = Matrix::new(4, 4, vec![1, 0, 6, 0, 0, 2, 0, 0, 0, 0, 1, 0, 5, 0, 0, 3]).expect("shape");

    for matrix in [&a, &b, &c] {
        let inverse = matrix.inverse(&ring).expect("invertible over F7");
        // §10.7 requires testing both the forward and inverse maps entrywise.
        assert!(
            matrix
                .mul(&ring, &inverse)
                .expect("product")
                .is_identity(&ring),
            "A * A^-1 != I"
        );
        assert!(
            inverse
                .mul(&ring, matrix)
                .expect("product")
                .is_identity(&ring),
            "A^-1 * A != I"
        );
    }

    let changed = map_factors(&decomposition, &a, &b, &c).expect("map");
    let restored = map_factors(
        &changed,
        &a.inverse(&ring).expect("inv"),
        &b.inverse(&ring).expect("inv"),
        &c.inverse(&ring).expect("inv"),
    )
    .expect("map back");

    for (left, right) in restored.terms().iter().zip(decomposition.terms()) {
        assert_eq!(left, right, "basis round trip changed a factor");
    }
    verify_decomposition(&restored).expect("restored decomposition reconstructs");
}

/// §12.5: factor normalization is idempotent where defined.
#[test]
fn normalization_is_idempotent() {
    let target = instance(2, 2, 2);

    let integer_ring = IntegerRing;
    let mut integer_terms = naive(target, integer_ring).into_terms();
    // Introduce a sign flip that unit normalization must canonicalize.
    for value in &mut integer_terms[0].u {
        *value = -value.clone();
    }
    for term in integer_terms {
        let once = normalize_term(&integer_ring, term).expect("normalize");
        let twice = normalize_term(&integer_ring, once.clone()).expect("normalize");
        assert_eq!(once, twice, "Z normalization is not idempotent");
    }

    let rational_ring = RationalRing;
    for term in naive(target, rational_ring).into_terms() {
        let once = normalize_term(&rational_ring, term).expect("normalize");
        let twice = normalize_term(&rational_ring, once.clone()).expect("normalize");
        assert_eq!(once, twice, "Q normalization is not idempotent");
    }
}

/// §10.4: normalization preserves the tensor sum.
#[test]
fn normalization_preserves_the_tensor_sum() {
    let ring = RationalRing;
    let target = instance(2, 2, 2);
    let decomposition = naive(target, ring);
    let before = tensor_sum(&ring, target, decomposition.terms());
    let mut normalized = decomposition.clone();
    normalized.normalize().expect("normalize");
    let after = tensor_sum(&ring, target, normalized.terms());
    assert_eq!(before, after, "normalization changed the tensor sum");
    assert!(normalized.is_canonically_ordered());
}

/// §12.5: term reordering canonicalizes identically.
#[test]
fn term_reordering_canonicalizes_identically() {
    let ring = IntegerRing;
    let target = instance(2, 2, 2);
    let decomposition = naive(target, ring);

    let mut forward = decomposition.clone();
    forward.normalize().expect("normalize");

    let mut reversed_terms = decomposition.into_terms();
    reversed_terms.reverse();
    let mut reversed = Decomposition::new(target, ring, reversed_terms).expect("valid");
    reversed.normalize().expect("normalize");

    assert_eq!(forward.terms(), reversed.terms());
}

/// §12.5 and B2: every flip preserves the tensor sum, in every mode.
#[test]
fn every_flip_preserves_the_tensor_sum() {
    let ring = IntegerRing;
    let target = instance(2, 2, 2);
    let terms = naive(target, ring).into_terms();

    let mut checked = 0;
    for shared in TensorMode::ALL {
        for i in 0..terms.len() {
            for j in 0..terms.len() {
                if i == j {
                    continue;
                }
                if terms[i].factor(shared) != terms[j].factor(shared) {
                    continue;
                }
                let (first, second) =
                    flip(&ring, &terms[i], &terms[j], shared).expect("shared factor");
                let mut moved = terms.clone();
                moved[i] = first;
                moved[j] = second;
                assert_eq!(
                    tensor_sum(&ring, target, &terms),
                    tensor_sum(&ring, target, &moved),
                    "flip in mode {:?} on ({i},{j}) changed the sum",
                    shared
                );
                checked += 1;
            }
        }
    }
    assert!(checked > 0, "the fixture must exercise real flips");
}

#[test]
fn flip_rejects_terms_that_do_not_share_the_named_factor() {
    let ring = IntegerRing;
    let terms = naive(instance(2, 2, 2), ring).into_terms();
    let error = flip(&ring, &terms[0], &terms[7], TensorMode::A).expect_err("no shared factor");
    assert_eq!(error.equation_id(), Some("B2"));
}

/// §12.5 and B3: every reduction preserves the tensor sum and does not increase
/// the term count.
#[test]
fn every_reduction_preserves_the_sum_and_does_not_grow() {
    let ring = IntegerRing;
    let target = instance(2, 2, 2);
    let mut terms = naive(target, ring).into_terms();
    // Duplicate a term so a genuine reduction exists.
    terms.push(terms[0].clone());
    let before = tensor_sum(&ring, target, &terms);

    let combined =
        reduce(&ring, &terms[0], &terms[terms.len() - 1], TensorMode::C).expect("shared u and v");
    let mut reduced = terms.clone();
    reduced.pop();
    reduced[0] = combined;

    assert!(reduced.len() < terms.len());
    assert_eq!(
        before,
        tensor_sum(&ring, target, &reduced),
        "reduction changed the sum"
    );
}

/// B4: a plus transition splits one term into two sum-equivalent terms.
#[test]
fn plus_transition_preserves_the_sum() {
    let ring = IntegerRing;
    let target = instance(2, 2, 2);
    let terms = naive(target, ring).into_terms();
    let before = tensor_sum(&ring, target, &terms);

    let part: Vec<Integer> = terms[0]
        .w
        .iter()
        .enumerate()
        .map(|(index, _)| Integer::from(if index == 0 { 5i32 } else { -2i32 }))
        .collect();
    let (first, second) = plus(&ring, &terms[0], TensorMode::C, &part).expect("same length");
    let mut split = terms.clone();
    split[0] = first;
    split.push(second);

    assert_eq!(
        split.len(),
        terms.len() + 1,
        "a plus transition adds a term"
    );
    assert_eq!(
        before,
        tensor_sum(&ring, target, &split),
        "plus transition changed the sum"
    );
}

#[test]
fn other_modes_is_the_canonical_complement() {
    assert_eq!(other_modes(TensorMode::A), [TensorMode::B, TensorMode::C]);
    assert_eq!(other_modes(TensorMode::B), [TensorMode::A, TensorMode::C]);
    assert_eq!(other_modes(TensorMode::C), [TensorMode::A, TensorMode::B]);
}

/// §6.6: a canonical term may not contain an all-zero factor.
#[test]
fn zero_factors_are_rejected_at_construction() {
    let ring = IntegerRing;
    let target = instance(2, 2, 2);
    let terms = vec![Term::new(
        vec![ring.zero(); 4],
        vec![ring.one(); 4],
        vec![ring.one(); 4],
    )];
    let error = Decomposition::new(target, ring, terms).expect_err("zero factor");
    assert_eq!(error.code(), mm_core::ErrorCode::ZeroFactor);
}

/// §6.6: factor lengths must match their tensor modes.
#[test]
fn wrong_factor_lengths_are_rejected_at_construction() {
    let ring = IntegerRing;
    let target = instance(2, 3, 4);
    let terms = vec![Term::new(
        vec![ring.one(); 6],
        vec![ring.one(); 12],
        vec![ring.one(); 7], // should be p*n = 8
    )];
    let error = Decomposition::new(target, ring, terms).expect_err("wrong length");
    assert_eq!(error.code(), mm_core::ErrorCode::WrongVectorLength);
}
