//! Rank-one terms, canonical normalization, and decomposition state
//! (spec §10.4, §6.6, Appendix B.1).
//!
//! Terminology is load-bearing (§10.4): this module tracks a **term count**,
//! never a proven tensor rank. An `R`-term decomposition proves
//! `rank(T) <= R` and nothing stronger.

use crate::ring::{ExactRing, RingTag};
use alloc::string::String;
use alloc::vec::Vec;
use mm_core::codes::ErrorCode;
use mm_core::dims::{MatMulInstance, TensorMode};
use mm_core::error::{CoreError, CoreResult};

/// One rank-one summand `u ⊗ v ⊗ w` (B1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term<E> {
    /// The left factor of length `nm`.
    pub u: Vec<E>,
    /// The right factor of length `mp`.
    pub v: Vec<E>,
    /// The dual-output factor of length `pn`.
    pub w: Vec<E>,
}

impl<E> Term<E> {
    /// Build a term from its three factors.
    #[must_use]
    pub const fn new(u: Vec<E>, v: Vec<E>, w: Vec<E>) -> Self {
        Self { u, v, w }
    }

    /// The factor for one tensor mode.
    #[must_use]
    pub fn factor(&self, mode: TensorMode) -> &[E] {
        match mode {
            TensorMode::A => &self.u,
            TensorMode::B => &self.v,
            TensorMode::C => &self.w,
        }
    }
}

/// A decomposition candidate over one exact ring.
#[derive(Clone, Debug)]
pub struct Decomposition<R: ExactRing> {
    instance: MatMulInstance,
    ring: R,
    terms: Vec<Term<R::Elem>>,
}

impl<R: ExactRing> Decomposition<R> {
    /// Build a decomposition, validating every factor length (§6.6).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::WrongVectorLength`] when a factor length disagrees
    /// with its tensor mode, and [`ErrorCode::ZeroFactor`] when a canonical term
    /// contains an all-zero factor.
    pub fn new(instance: MatMulInstance, ring: R, terms: Vec<Term<R::Elem>>) -> CoreResult<Self> {
        let lengths = [
            instance.mode_len(TensorMode::A)?,
            instance.mode_len(TensorMode::B)?,
            instance.mode_len(TensorMode::C)?,
        ];
        for (index, term) in terms.iter().enumerate() {
            for (mode, expected) in TensorMode::ALL.into_iter().zip(lengths) {
                let actual = term.factor(mode).len();
                if actual != expected {
                    return Err(CoreError::new(
                        ErrorCode::WrongVectorLength,
                        "a decomposition factor has the wrong length for its tensor mode",
                    )
                    .equation("§6.6")
                    .value(alloc::format!(
                        "term {index} factor {} has length {actual}, expected {expected}",
                        mode.name()
                    )));
                }
            }
            for mode in TensorMode::ALL {
                if ring.is_zero_vector(term.factor(mode)) {
                    return Err(CoreError::new(
                        ErrorCode::ZeroFactor,
                        "a canonical term must not contain an all-zero factor",
                    )
                    .equation("§6.6")
                    .value(alloc::format!("term {index} factor {}", mode.name())));
                }
            }
        }
        Ok(Self {
            instance,
            ring,
            terms,
        })
    }

    /// The instance this decomposition targets.
    #[must_use]
    pub const fn instance(&self) -> MatMulInstance {
        self.instance
    }

    /// The coefficient ring.
    #[must_use]
    pub const fn ring(&self) -> &R {
        &self.ring
    }

    /// The ring tag.
    #[must_use]
    pub fn ring_tag(&self) -> RingTag {
        self.ring.tag()
    }

    /// The terms in their current order.
    #[must_use]
    pub fn terms(&self) -> &[Term<R::Elem>] {
        &self.terms
    }

    /// The number of terms.
    ///
    /// This is a **term count**, not a proven tensor rank (§10.4).
    #[must_use]
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// Consume into the term list.
    #[must_use]
    pub fn into_terms(self) -> Vec<Term<R::Elem>> {
        self.terms
    }

    /// The canonical byte encoding of one term, used for ordering (§10.4).
    ///
    /// The encoding is the canonical JSON array of the three factor arrays, so
    /// the byte-lexicographic order it induces is reproducible in Lean and Rust
    /// from the same definition.
    #[must_use]
    pub fn term_bytes(ring: &R, term: &Term<R::Elem>) -> String {
        let mut out = String::from("[");
        for (mode_index, mode) in TensorMode::ALL.into_iter().enumerate() {
            if mode_index > 0 {
                out.push(',');
            }
            out.push('[');
            for (index, value) in term.factor(mode).iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                out.push_str(&ring.encode_json(value));
            }
            out.push(']');
        }
        out.push(']');
        out
    }

    /// Apply the canonical normalization of §10.4.
    ///
    /// 1. remove a term if any factor is zero;
    /// 2. normalize coefficients by the ring-specific rule;
    /// 3. sort terms lexicographically by canonical coefficient bytes; and
    /// 4. retain multiplicity — duplicate terms are **not** discarded, because
    ///    only exact ring addition may justify a reduction.
    ///
    /// # Errors
    ///
    /// Propagates ring inversion failures.
    pub fn normalize(&mut self) -> CoreResult<()> {
        let ring = self.ring.clone();
        let mut kept: Vec<Term<R::Elem>> = Vec::with_capacity(self.terms.len());
        for term in self.terms.drain(..) {
            if TensorMode::ALL
                .into_iter()
                .any(|mode| ring.is_zero_vector(term.factor(mode)))
            {
                continue;
            }
            kept.push(normalize_term(&ring, term)?);
        }
        kept.sort_by(|left, right| {
            Self::term_bytes(&ring, left).cmp(&Self::term_bytes(&ring, right))
        });
        self.terms = kept;
        Ok(())
    }

    /// Whether the terms are already in canonical sorted order (§10.4).
    #[must_use]
    pub fn is_canonically_ordered(&self) -> bool {
        self.terms.windows(2).all(|pair| {
            Self::term_bytes(&self.ring, &pair[0]) <= Self::term_bytes(&self.ring, &pair[1])
        })
    }

    /// Reject a decomposition whose terms are not canonically ordered (§10.4).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalTermOrder`] when the order is wrong.
    pub fn require_canonical_order(&self) -> CoreResult<()> {
        if self.is_canonically_ordered() {
            Ok(())
        } else {
            Err(CoreError::new(
                ErrorCode::NoncanonicalTermOrder,
                "terms must be sorted lexicographically by canonical coefficient bytes",
            )
            .equation("§10.4"))
        }
    }
}

/// Normalize one term's coefficients by the ring rule (§10.4).
///
/// `u` is divided by its first nonzero coefficient `a`, `v` by its first nonzero
/// coefficient `b`, and `w` is replaced by `ab·w`. For `Z` the normalizers are
/// the signs of those coefficients, which is exactly the permitted unit scaling.
///
/// # Errors
///
/// Propagates ring inversion failures.
pub fn normalize_term<R: ExactRing>(ring: &R, term: Term<R::Elem>) -> CoreResult<Term<R::Elem>> {
    let Term { u, v, w } = term;
    let a = ring.normalizer(&u);
    let b = ring.normalizer(&v);
    match (a, b) {
        (Some(a), Some(b)) => {
            let u = ring.scale_inverse(&u, &a)?;
            let v = ring.scale_inverse(&v, &b)?;
            let scalar = ring.mul(&a, &b);
            let w = ring.scale(&w, &scalar);
            Ok(Term::new(u, v, w))
        }
        // An all-zero factor is removed before normalization; reaching here means
        // the caller kept a degenerate term, so pass it through unchanged rather
        // than inventing a scalar.
        _ => Ok(Term::new(u, v, w)),
    }
}
