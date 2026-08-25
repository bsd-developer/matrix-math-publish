//! Change of basis on decompositions and tensors (spec §10.7, Appendix B.5–B.6).
//!
//! With invertible `A`, `B`, `C`,
//!
//! ```text
//! T'[i,j,k] = sum_(a,b,c) A[i,a] B[j,b] C[k,c] T[a,b,c]      (B5)
//! T        = (A^-1 (x) B^-1 (x) C^-1) T'                     (B6)
//! ```
//!
//! so a decomposition of `T'` maps back to canonical coordinates by applying the
//! inverse maps factorwise. The inverse is always made explicit: §10.7 forbids
//! leaving it implicit, and every test checks both directions entrywise.

use crate::decomposition::{Decomposition, Term};
use crate::ring::ExactRing;
use alloc::vec;
use alloc::vec::Vec;
use mm_core::codes::ErrorCode;
use mm_core::dims::TensorMode;
use mm_core::error::{CoreError, CoreResult};

/// A dense row-major matrix over an exact ring.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Matrix<E> {
    rows: usize,
    cols: usize,
    data: Vec<E>,
}

impl<E: Clone> Matrix<E> {
    /// Build a matrix from row-major data.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::WrongVectorLength`] when `data.len() != rows*cols`.
    pub fn new(rows: usize, cols: usize, data: Vec<E>) -> CoreResult<Self> {
        let expected = rows.checked_mul(cols).ok_or_else(|| {
            CoreError::new(ErrorCode::ArithmeticOverflow, "matrix size overflowed")
        })?;
        if data.len() != expected {
            return Err(CoreError::new(
                ErrorCode::WrongVectorLength,
                "matrix data length does not match its shape",
            )
            .equation("§10.7"));
        }
        Ok(Self { rows, cols, data })
    }

    /// The number of rows.
    #[must_use]
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// The number of columns.
    #[must_use]
    pub const fn cols(&self) -> usize {
        self.cols
    }

    /// The entry at `(row, col)`, or `None` when out of range.
    #[must_use]
    pub fn get(&self, row: usize, col: usize) -> Option<&E> {
        if row >= self.rows || col >= self.cols {
            return None;
        }
        self.data.get(row * self.cols + col)
    }

    /// The `size x size` identity matrix.
    #[must_use]
    pub fn identity<R: ExactRing<Elem = E>>(ring: &R, size: usize) -> Self {
        let mut data = vec![ring.zero(); size * size];
        for index in 0..size {
            if let Some(slot) = data.get_mut(index * size + index) {
                *slot = ring.one();
            }
        }
        Self {
            rows: size,
            cols: size,
            data,
        }
    }
}

impl<E: Clone + Eq> Matrix<E> {
    /// The matrix-vector product `self * vector`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::WrongVectorLength`] on a dimension mismatch.
    pub fn apply<R: ExactRing<Elem = E>>(&self, ring: &R, vector: &[E]) -> CoreResult<Vec<E>> {
        if vector.len() != self.cols {
            return Err(CoreError::new(
                ErrorCode::WrongVectorLength,
                "matrix-vector product dimension mismatch",
            )
            .equation("§10.7"));
        }
        let mut out = Vec::with_capacity(self.rows);
        for row in 0..self.rows {
            let mut total = ring.zero();
            for (col, value) in vector.iter().enumerate() {
                if ring.is_zero(value) {
                    continue;
                }
                if let Some(entry) = self.get(row, col) {
                    total = ring.add(&total, &ring.mul(entry, value));
                }
            }
            out.push(total);
        }
        Ok(out)
    }

    /// The matrix product `self * other`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::WrongVectorLength`] on a dimension mismatch.
    pub fn mul<R: ExactRing<Elem = E>>(&self, ring: &R, other: &Self) -> CoreResult<Self> {
        if self.cols != other.rows {
            return Err(CoreError::new(
                ErrorCode::WrongVectorLength,
                "matrix product dimension mismatch",
            )
            .equation("§10.7"));
        }
        let mut data = Vec::with_capacity(self.rows * other.cols);
        for row in 0..self.rows {
            for col in 0..other.cols {
                let mut total = ring.zero();
                for index in 0..self.cols {
                    if let (Some(left), Some(right)) = (self.get(row, index), other.get(index, col))
                    {
                        total = ring.add(&total, &ring.mul(left, right));
                    }
                }
                data.push(total);
            }
        }
        Self::new(self.rows, other.cols, data)
    }

    /// Whether this matrix is the identity.
    #[must_use]
    pub fn is_identity<R: ExactRing<Elem = E>>(&self, ring: &R) -> bool {
        if self.rows != self.cols {
            return false;
        }
        let one = ring.one();
        let zero = ring.zero();
        (0..self.rows).all(|row| {
            (0..self.cols).all(|col| {
                let expected = if row == col { &one } else { &zero };
                self.get(row, col) == Some(expected)
            })
        })
    }

    /// The inverse by Gauss-Jordan elimination over a field.
    ///
    /// Returns `None` when a pivot is not invertible in the ring, which for `Z`
    /// means anything other than a unit pivot. Integer search therefore samples
    /// unimodular matrices whose inverses are known by construction (§10.7).
    #[must_use]
    pub fn inverse<R: ExactRing<Elem = E>>(&self, ring: &R) -> Option<Self> {
        if self.rows != self.cols {
            return None;
        }
        let size = self.rows;
        let mut left = self.data.clone();
        let mut right = Self::identity(ring, size).data;

        for pivot in 0..size {
            let mut selected = None;
            for row in pivot..size {
                if let Some(value) = left.get(row * size + pivot)
                    && !ring.is_zero(value)
                    && ring.inverse(value).is_some()
                {
                    selected = Some(row);
                    break;
                }
            }
            let row = selected?;
            if row != pivot {
                for col in 0..size {
                    left.swap(row * size + col, pivot * size + col);
                    right.swap(row * size + col, pivot * size + col);
                }
            }
            let pivot_value = left.get(pivot * size + pivot)?.clone();
            let pivot_inverse = ring.inverse(&pivot_value)?;
            for col in 0..size {
                if let Some(slot) = left.get_mut(pivot * size + col) {
                    *slot = ring.mul(slot, &pivot_inverse);
                }
                if let Some(slot) = right.get_mut(pivot * size + col) {
                    *slot = ring.mul(slot, &pivot_inverse);
                }
            }
            for row in 0..size {
                if row == pivot {
                    continue;
                }
                let factor = left.get(row * size + pivot)?.clone();
                if ring.is_zero(&factor) {
                    continue;
                }
                for col in 0..size {
                    let left_pivot = left.get(pivot * size + col)?.clone();
                    if let Some(slot) = left.get_mut(row * size + col) {
                        *slot = ring.sub(slot, &ring.mul(&factor, &left_pivot));
                    }
                    let right_pivot = right.get(pivot * size + col)?.clone();
                    if let Some(slot) = right.get_mut(row * size + col) {
                        *slot = ring.sub(slot, &ring.mul(&factor, &right_pivot));
                    }
                }
            }
        }
        Self::new(size, size, right).ok()
    }
}

/// Apply the factorwise maps `(a, b, c)` to every term of a decomposition.
///
/// Passing the inverse triple recovers canonical coordinates from a
/// changed-basis decomposition (B6). The term count is unchanged.
///
/// # Errors
///
/// Propagates dimension mismatches and revalidates the resulting decomposition.
pub fn map_factors<R: ExactRing>(
    decomposition: &Decomposition<R>,
    a: &Matrix<R::Elem>,
    b: &Matrix<R::Elem>,
    c: &Matrix<R::Elem>,
) -> CoreResult<Decomposition<R>> {
    let ring = decomposition.ring().clone();
    let mut terms = Vec::with_capacity(decomposition.term_count());
    for term in decomposition.terms() {
        terms.push(Term::new(
            a.apply(&ring, term.factor(TensorMode::A))?,
            b.apply(&ring, term.factor(TensorMode::B))?,
            c.apply(&ring, term.factor(TensorMode::C))?,
        ));
    }
    Decomposition::new(decomposition.instance(), ring, terms)
}
