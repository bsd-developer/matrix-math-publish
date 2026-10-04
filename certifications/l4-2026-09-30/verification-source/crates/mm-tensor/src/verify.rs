//! Streaming reconstruction checking against `T_{n,m,p}` (spec §10.1, B1).
//!
//! The check never materializes the dense `nm x mp x pn` tensor. For each pair
//! of first-mode and second-mode coordinates it forms the vector of bilinear
//! coefficients and accumulates the third-mode column, then compares that column
//! against the exact target column, which the §10.1 definition makes available in
//! closed form: the column is entirely zero unless the two contraction indices
//! agree, in which case it holds a single one.
//!
//! Cost is `O(nm · mp · (R + pn))` with early exit, and working memory is
//! `O(R + pn)`.

use crate::decomposition::Decomposition;
use crate::ring::ExactRing;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;
use mm_core::codes::ErrorCode;
use mm_core::dims::{MatMulInstance, TensorMode};
use mm_core::error::{CoreError, CoreResult};

/// The verified conclusion of a decomposition check (§10.4, B1).
///
/// The claim is deliberately an upper bound: the checker proves reconstruction,
/// never minimality.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecompositionClaim {
    /// The instance whose tensor was reconstructed.
    pub instance: MatMulInstance,
    /// The number of normalized nonzero terms.
    pub term_count: usize,
}

impl DecompositionClaim {
    /// The human-readable claim text used in reports and manifests.
    #[must_use]
    pub fn statement(&self) -> alloc::string::String {
        format!(
            "rank(T[{},{},{}]) <= {}",
            self.instance.n(),
            self.instance.m(),
            self.instance.p(),
            self.term_count
        )
    }
}

/// The exact entry of `T_{n,m,p}` at flattened coordinates (§10.1, B.1).
///
/// Returns one exactly when the coordinates decode to `(i,k)`, `(k,j)`, and the
/// dual `(j,i)` with matching `i`, `j`, and `k`; otherwise zero.
///
/// # Errors
///
/// Returns [`ErrorCode::UnsupportedInstance`] for an out-of-range coordinate.
pub fn target_entry(instance: MatMulInstance, a: usize, b: usize, c: usize) -> CoreResult<bool> {
    let (i, k) = instance.unflat_a(a)?;
    let (k2, j) = instance.unflat_b(b)?;
    let (j2, i2) = instance.unflat_c_dual(c)?;
    Ok(k == k2 && j == j2 && i == i2)
}

/// Iterate the support of `T_{n,m,p}`: the `n·m·p` coordinates whose entry is one.
///
/// # Errors
///
/// Propagates flattening failures.
pub fn target_support(instance: MatMulInstance) -> CoreResult<Vec<(usize, usize, usize)>> {
    let mut out = Vec::new();
    for i in 0..instance.n().as_usize() {
        for k in 0..instance.m().as_usize() {
            for j in 0..instance.p().as_usize() {
                out.push((
                    instance.flat_a(i, k)?,
                    instance.flat_b(k, j)?,
                    instance.flat_c_dual(j, i)?,
                ));
            }
        }
    }
    Ok(out)
}

/// Verify `T_{n,m,p} = Σ_r u_r ⊗ v_r ⊗ w_r` entrywise in the stated ring (B1).
///
/// The first disagreement is returned deterministically, with the offending
/// coordinates and both exact values (§5.4).
///
/// # Errors
///
/// Returns [`ErrorCode::ReconstructionMismatch`] on the first differing entry.
pub fn verify_decomposition<R: ExactRing>(
    decomposition: &Decomposition<R>,
) -> CoreResult<DecompositionClaim> {
    let instance = decomposition.instance();
    let ring = decomposition.ring();
    let len_a = instance.mode_len(TensorMode::A)?;
    let len_b = instance.mode_len(TensorMode::B)?;
    let len_c = instance.mode_len(TensorMode::C)?;
    let terms = decomposition.terms();

    let zero = ring.zero();
    let one = ring.one();
    let mut column: Vec<R::Elem> = vec![zero.clone(); len_c];

    for a in 0..len_a {
        let (i, k) = instance.unflat_a(a)?;
        for b in 0..len_b {
            let (k2, j) = instance.unflat_b(b)?;

            for slot in column.iter_mut() {
                slot.clone_from(&zero);
            }
            for term in terms {
                let ua = term.u.get(a).ok_or_else(|| length_error("u"))?;
                if ring.is_zero(ua) {
                    continue;
                }
                let vb = term.v.get(b).ok_or_else(|| length_error("v"))?;
                if ring.is_zero(vb) {
                    continue;
                }
                let coefficient = ring.mul(ua, vb);
                if ring.is_zero(&coefficient) {
                    continue;
                }
                for (slot, wc) in column.iter_mut().zip(term.w.iter()) {
                    let contribution = ring.mul(&coefficient, wc);
                    if !ring.is_zero(&contribution) {
                        *slot = ring.add(slot, &contribution);
                    }
                }
            }

            // The target column: zero unless the contraction indices agree, in
            // which case it is the indicator of the dual coordinate (j,i).
            let hot = if k == k2 {
                Some(instance.flat_c_dual(j, i)?)
            } else {
                None
            };
            for (c, actual) in column.iter().enumerate() {
                let expected = if Some(c) == hot { &one } else { &zero };
                if actual != expected {
                    return Err(CoreError::new(
                        ErrorCode::ReconstructionMismatch,
                        "the decomposition does not reconstruct the target tensor",
                    )
                    .equation("B1")
                    .value(format!("coordinate (a={a}, b={b}, c={c})"))
                    .value(format!("expected {}", ring.encode(expected)))
                    .value(format!("actual {}", ring.encode(actual))));
                }
            }
        }
    }

    Ok(DecompositionClaim {
        instance,
        term_count: decomposition.term_count(),
    })
}

fn length_error(factor: &str) -> CoreError {
    CoreError::new(
        ErrorCode::WrongVectorLength,
        "a decomposition factor is shorter than its tensor mode",
    )
    .equation("§6.6")
    .value(alloc::string::String::from(factor))
}
