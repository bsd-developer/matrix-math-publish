//! Tensor-mode isomorphisms (spec §12.5, Appendix B.3).
//!
//! Both maps are pure index relabelings: they permute which flattened
//! coordinate each factor entry occupies without touching a coefficient, so a
//! valid decomposition maps to a valid decomposition with the same term count.
//! §12.5 makes them mandatory metamorphic properties, and §10.3 requires the
//! index maps to be explicit rather than inferred.

use crate::decomposition::{Decomposition, Term};
use crate::ring::ExactRing;
use alloc::vec;
use alloc::vec::Vec;
use mm_core::dims::{MatMulInstance, TensorMode};
use mm_core::error::CoreResult;

/// The cyclic mode shift `T[n,m,p] -> T[m,p,n]`.
///
/// The support of `T[n,m,p]` is `(i*m+k, k*p+j, j*n+i)`. Substituting
/// `i' = k, k' = j, j' = i` turns it into `(i'*p+k', k'*n+j', j'*m+i')`, which is
/// exactly the support of `T[m,p,n]`. So the factor triple simply rotates.
///
/// # Errors
///
/// Propagates instance construction failures.
pub fn cyclic_shift<R: ExactRing>(
    decomposition: &Decomposition<R>,
) -> CoreResult<Decomposition<R>> {
    let instance = decomposition.instance();
    let shifted = MatMulInstance::new(instance.m(), instance.p(), instance.n())?;
    let terms = decomposition
        .terms()
        .iter()
        .map(|term| Term::new(term.v.clone(), term.w.clone(), term.u.clone()))
        .collect();
    Decomposition::new(shifted, decomposition.ring().clone(), terms)
}

/// The transpose isomorphism `T[n,m,p] -> T[p,m,n]`, from `(AB)^T = B^T A^T`.
///
/// Explicitly, with primes denoting the image instance:
///
/// ```text
/// u'[j*m + k] = v[k*p + j]
/// v'[k*n + i] = u[i*m + k]
/// w'[i*p + j] = w[j*n + i]
/// ```
///
/// # Errors
///
/// Propagates instance construction and flattening failures.
pub fn transpose<R: ExactRing>(decomposition: &Decomposition<R>) -> CoreResult<Decomposition<R>> {
    let instance = decomposition.instance();
    let image = MatMulInstance::new(instance.p(), instance.m(), instance.n())?;
    let ring = decomposition.ring().clone();
    let n = instance.n().as_usize();
    let m = instance.m().as_usize();
    let p = instance.p().as_usize();

    let mut terms = Vec::with_capacity(decomposition.term_count());
    for term in decomposition.terms() {
        let mut u = vec![ring.zero(); image.mode_len(TensorMode::A)?];
        let mut v = vec![ring.zero(); image.mode_len(TensorMode::B)?];
        let mut w = vec![ring.zero(); image.mode_len(TensorMode::C)?];
        for k in 0..m {
            for j in 0..p {
                if let (Some(target), Some(source)) = (u.get_mut(j * m + k), term.v.get(k * p + j))
                {
                    target.clone_from(source);
                }
            }
        }
        for i in 0..n {
            for k in 0..m {
                if let (Some(target), Some(source)) = (v.get_mut(k * n + i), term.u.get(i * m + k))
                {
                    target.clone_from(source);
                }
            }
        }
        for i in 0..n {
            for j in 0..p {
                if let (Some(target), Some(source)) = (w.get_mut(i * p + j), term.w.get(j * n + i))
                {
                    target.clone_from(source);
                }
            }
        }
        terms.push(Term::new(u, v, w));
    }
    Decomposition::new(image, ring, terms)
}
