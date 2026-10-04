//! Sum-preserving local moves on decompositions (spec §10.5, Appendix B.2–B.4).
//!
//! Moves are constructed from the algebraic identities, never by editing tensor
//! entries directly (B.5). Each identity is stated once here and proved in
//! `lean/MatrixMath/Spec/Tensor.lean`; the property tests in
//! `tests/moves.rs` check that every move preserves the exact tensor sum.

use crate::decomposition::Term;
use crate::ring::ExactRing;
use alloc::vec::Vec;
use mm_core::codes::ErrorCode;
use mm_core::dims::TensorMode;
use mm_core::error::{CoreError, CoreResult};

/// The two terms a sum-preserving move produces from one pair or one term.
pub type TermPair<R> = (Term<<R as ExactRing>::Elem>, Term<<R as ExactRing>::Elem>);

/// The flip identity B2, generalized to a shared factor in any tensor mode.
///
/// With the shared factor in mode `shared` and the two remaining modes taken in
/// canonical order as `Y` then `Z`, the pair
///
/// ```text
/// (s, y1, z1) + (s, y2, z2)
/// ```
///
/// is replaced by
///
/// ```text
/// (s, y1 + y2, z1) + (s, y2, z2 - z1).
/// ```
///
/// Expanding by distributivity shows the tensor sum is preserved exactly. In
/// characteristic two subtraction equals addition, so the same code covers `F2`.
///
/// # Errors
///
/// Returns [`ErrorCode::ReconstructionMismatch`] when the two terms do not
/// actually share the named factor, since applying the identity would then not
/// preserve the sum.
pub fn flip<R: ExactRing>(
    ring: &R,
    first: &Term<R::Elem>,
    second: &Term<R::Elem>,
    shared: TensorMode,
) -> CoreResult<TermPair<R>> {
    if first.factor(shared) != second.factor(shared) {
        return Err(CoreError::new(
            ErrorCode::ReconstructionMismatch,
            "a flip requires the two terms to share the named factor",
        )
        .equation("B2"));
    }
    let [y_mode, z_mode] = other_modes(shared);
    let y1 = first.factor(y_mode);
    let y2 = second.factor(y_mode);
    let z1 = first.factor(z_mode);
    let z2 = second.factor(z_mode);

    let y_sum: Vec<R::Elem> = y1
        .iter()
        .zip(y2.iter())
        .map(|(left, right)| ring.add(left, right))
        .collect();
    let z_difference: Vec<R::Elem> = z2
        .iter()
        .zip(z1.iter())
        .map(|(left, right)| ring.sub(left, right))
        .collect();

    let new_first = assemble(shared, first.factor(shared).to_vec(), y_sum, z1.to_vec());
    let new_second = assemble(
        shared,
        second.factor(shared).to_vec(),
        y2.to_vec(),
        z_difference,
    );
    Ok((new_first, new_second))
}

/// The reduction identity B3: two terms sharing **two** factors combine into one.
///
/// ```text
/// a (x) b (x) c1 + a (x) b (x) c2 = a (x) b (x) (c1 + c2)
/// ```
///
/// A reduction never increases the term count (§10.5).
///
/// # Errors
///
/// Returns [`ErrorCode::ReconstructionMismatch`] when the terms do not share the
/// two named factors.
pub fn reduce<R: ExactRing>(
    ring: &R,
    first: &Term<R::Elem>,
    second: &Term<R::Elem>,
    combined: TensorMode,
) -> CoreResult<Term<R::Elem>> {
    let [other_a, other_b] = other_modes(combined);
    if first.factor(other_a) != second.factor(other_a)
        || first.factor(other_b) != second.factor(other_b)
    {
        return Err(CoreError::new(
            ErrorCode::ReconstructionMismatch,
            "a reduction requires the two terms to share their other two factors",
        )
        .equation("B3"));
    }
    let sum: Vec<R::Elem> = first
        .factor(combined)
        .iter()
        .zip(second.factor(combined).iter())
        .map(|(left, right)| ring.add(left, right))
        .collect();
    Ok(assemble(
        combined,
        sum,
        first.factor(other_a).to_vec(),
        first.factor(other_b).to_vec(),
    ))
}

/// The plus identity B4: split one term into two sum-equivalent terms.
///
/// ```text
/// a (x) b (x) c = a (x) b (x) c' + a (x) b (x) (c - c')
/// ```
///
/// Plus transitions increase the term count before normalization and are
/// disabled in the baseline search, enabled only by explicit configuration
/// (§10.5).
///
/// # Errors
///
/// Returns [`ErrorCode::WrongVectorLength`] when `part` has the wrong length.
pub fn plus<R: ExactRing>(
    ring: &R,
    term: &Term<R::Elem>,
    split: TensorMode,
    part: &[R::Elem],
) -> CoreResult<TermPair<R>> {
    let original = term.factor(split);
    if part.len() != original.len() {
        return Err(CoreError::new(
            ErrorCode::WrongVectorLength,
            "a plus transition needs a part of the same length as the split factor",
        )
        .equation("B4"));
    }
    let remainder: Vec<R::Elem> = original
        .iter()
        .zip(part.iter())
        .map(|(whole, piece)| ring.sub(whole, piece))
        .collect();
    let [other_a, other_b] = other_modes(split);
    let first = assemble(
        split,
        part.to_vec(),
        term.factor(other_a).to_vec(),
        term.factor(other_b).to_vec(),
    );
    let second = assemble(
        split,
        remainder,
        term.factor(other_a).to_vec(),
        term.factor(other_b).to_vec(),
    );
    Ok((first, second))
}

/// The two modes other than `mode`, in canonical `A < B < C` order.
#[must_use]
pub const fn other_modes(mode: TensorMode) -> [TensorMode; 2] {
    match mode {
        TensorMode::A => [TensorMode::B, TensorMode::C],
        TensorMode::B => [TensorMode::A, TensorMode::C],
        TensorMode::C => [TensorMode::A, TensorMode::B],
    }
}

/// Rebuild a term from a distinguished mode's factor and the other two, given in
/// the canonical order produced by [`other_modes`].
fn assemble<E>(mode: TensorMode, primary: Vec<E>, first: Vec<E>, second: Vec<E>) -> Term<E> {
    match mode {
        TensorMode::A => Term::new(primary, first, second),
        TensorMode::B => Term::new(first, primary, second),
        TensorMode::C => Term::new(first, second, primary),
    }
}
