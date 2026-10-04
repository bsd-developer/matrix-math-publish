//! Bridging between search state and certificate representation (spec §17.7).
//!
//! The search uses a bit-packed `𝔽₂` state for speed; a certificate uses the
//! `mm-tensor` decomposition model. §17.7 permits search code to depend on core,
//! schema, and tensor **types**, so the conversion lives here rather than in the
//! CLI, where it could not be property-tested.
//!
//! The conversion is not trusted for anything: a converted state is a candidate
//! until the checker accepts its canonical bytes.

use crate::f2::{F2State, F2Term, F2Vec};
use mm_core::dims::TensorMode;
use mm_core::error::CoreResult;
use mm_tensor::decomposition::{Decomposition, Term};
use mm_tensor::ring::PrimeField;

/// Convert a bit-packed `𝔽₂` state into a certificate-ready decomposition.
///
/// # Errors
///
/// Propagates mode-length and validation failures.
pub fn state_to_decomposition(state: &F2State) -> CoreResult<Decomposition<PrimeField>> {
    let instance = state.instance();
    let lengths = [
        instance.mode_len(TensorMode::A)?,
        instance.mode_len(TensorMode::B)?,
        instance.mode_len(TensorMode::C)?,
    ];
    let to_vec = |vector: F2Vec, len: usize| -> Vec<u32> {
        vector.to_bits(len).into_iter().map(u32::from).collect()
    };
    let mut terms = Vec::with_capacity(state.term_count());
    for term in state.terms() {
        terms.push(Term::new(
            to_vec(term.u, lengths[0]),
            to_vec(term.v, lengths[1]),
            to_vec(term.w, lengths[2]),
        ));
    }
    let mut decomposition = Decomposition::new(instance, PrimeField::f2(), terms)?;
    decomposition.normalize()?;
    Ok(decomposition)
}

/// Convert a certificate-ready decomposition back into search state.
///
/// # Errors
///
/// Propagates state construction failures.
pub fn decomposition_to_state(decomposition: &Decomposition<PrimeField>) -> CoreResult<F2State> {
    let to_vec = |values: &[u32]| F2Vec::from_bits(values.iter().map(|value| *value != 0));
    let mut terms = Vec::with_capacity(decomposition.term_count());
    for term in decomposition.terms() {
        terms.push(F2Term::new(
            to_vec(&term.u)?,
            to_vec(&term.v)?,
            to_vec(&term.w)?,
        ));
    }
    F2State::new(decomposition.instance(), terms)
}
