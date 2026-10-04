//! Matrix-multiplication instance dimensions and the normative flattening
//! (spec §0.2, §10.1, Appendix B.1).
//!
//! The third tensor mode is explicitly the **dual** output coordinate `(j,i)`,
//! not `(i,j)`. Getting this wrong silently transposes every result, so the
//! flattening functions are written once here and every other crate calls them
//! rather than re-deriving an index expression (ADR 0007).

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult, overflow};
use alloc::format;
use core::fmt;

/// The largest tensor dimension version 1 accepts (§0.2).
pub const MAX_DIM: u16 = 12;

/// A validated tensor dimension in `1..=12` (§0.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Dim(u16);

impl Dim {
    /// Construct a dimension, rejecting anything outside `1..=12`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] outside the supported range.
    pub fn new(value: u16) -> CoreResult<Self> {
        if (1..=MAX_DIM).contains(&value) {
            Ok(Self(value))
        } else {
            Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!("tensor dimensions must be in 1..={MAX_DIM}"),
            )
            .equation("§0.2")
            .value(format!("{value}")))
        }
    }

    /// The underlying integer.
    #[must_use]
    pub const fn get(self) -> u16 {
        self.0
    }

    /// The underlying integer as a `usize`.
    #[must_use]
    pub const fn as_usize(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A validated `n x m` by `m x p` matrix-multiplication instance (§10.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MatMulInstance {
    n: Dim,
    m: Dim,
    p: Dim,
}

impl MatMulInstance {
    /// Construct an instance from three validated dimensions.
    ///
    /// The mode sizes `nm`, `mp`, and `pn` are computed with checked arithmetic
    /// here so that later allocation sites cannot overflow (§0.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ArithmeticOverflow`] if any mode size overflows.
    pub fn new(n: Dim, m: Dim, p: Dim) -> CoreResult<Self> {
        let instance = Self { n, m, p };
        // Force the checked products now rather than at first use.
        let _ = instance.mode_len(TensorMode::A)?;
        let _ = instance.mode_len(TensorMode::B)?;
        let _ = instance.mode_len(TensorMode::C)?;
        Ok(instance)
    }

    /// Construct from raw integers, validating each dimension.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] for an out-of-range dimension.
    pub fn from_raw(n: u16, m: u16, p: u16) -> CoreResult<Self> {
        Self::new(Dim::new(n)?, Dim::new(m)?, Dim::new(p)?)
    }

    /// The `n` dimension (rows of `A`, rows of `C`).
    #[must_use]
    pub const fn n(self) -> Dim {
        self.n
    }

    /// The `m` dimension (shared inner dimension).
    #[must_use]
    pub const fn m(self) -> Dim {
        self.m
    }

    /// The `p` dimension (columns of `B`, columns of `C`).
    #[must_use]
    pub const fn p(self) -> Dim {
        self.p
    }

    /// The length of one tensor mode: `nm`, `mp`, or `pn` (§10.1).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ArithmeticOverflow`] on overflow.
    pub fn mode_len(self, mode: TensorMode) -> CoreResult<usize> {
        let (left, right) = match mode {
            TensorMode::A => (self.n, self.m),
            TensorMode::B => (self.m, self.p),
            TensorMode::C => (self.p, self.n),
        };
        left.as_usize()
            .checked_mul(right.as_usize())
            .ok_or_else(|| overflow("MatMulInstance::mode_len"))
    }

    /// The total number of tensor entries `nm * mp * pn`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ArithmeticOverflow`] on overflow.
    pub fn entry_count(self) -> CoreResult<usize> {
        let a = self.mode_len(TensorMode::A)?;
        let b = self.mode_len(TensorMode::B)?;
        let c = self.mode_len(TensorMode::C)?;
        a.checked_mul(b)
            .and_then(|partial| partial.checked_mul(c))
            .ok_or_else(|| overflow("MatMulInstance::entry_count"))
    }

    /// `flatA(i,k) = i*m + k` for `0 <= i < n`, `0 <= k < m` (§10.1).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when an index is out of range.
    pub fn flat_a(self, i: usize, k: usize) -> CoreResult<usize> {
        self.check_index("i", i, self.n)?;
        self.check_index("k", k, self.m)?;
        Ok(i * self.m.as_usize() + k)
    }

    /// `flatB(k,j) = k*p + j` for `0 <= k < m`, `0 <= j < p` (§10.1).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when an index is out of range.
    pub fn flat_b(self, k: usize, j: usize) -> CoreResult<usize> {
        self.check_index("k", k, self.m)?;
        self.check_index("j", j, self.p)?;
        Ok(k * self.p.as_usize() + j)
    }

    /// `flatCdual(j,i) = j*n + i` for `0 <= j < p`, `0 <= i < n` (§10.1).
    ///
    /// Note the argument order: the **dual** output coordinate is `(j,i)`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when an index is out of range.
    pub fn flat_c_dual(self, j: usize, i: usize) -> CoreResult<usize> {
        self.check_index("j", j, self.p)?;
        self.check_index("i", i, self.n)?;
        Ok(j * self.n.as_usize() + i)
    }

    /// Invert [`Self::flat_a`], returning `(i,k)`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when the index is out of range.
    pub fn unflat_a(self, index: usize) -> CoreResult<(usize, usize)> {
        let len = self.mode_len(TensorMode::A)?;
        self.check_flat(index, len, "A")?;
        Ok((index / self.m.as_usize(), index % self.m.as_usize()))
    }

    /// Invert [`Self::flat_b`], returning `(k,j)`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when the index is out of range.
    pub fn unflat_b(self, index: usize) -> CoreResult<(usize, usize)> {
        let len = self.mode_len(TensorMode::B)?;
        self.check_flat(index, len, "B")?;
        Ok((index / self.p.as_usize(), index % self.p.as_usize()))
    }

    /// Invert [`Self::flat_c_dual`], returning `(j,i)`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when the index is out of range.
    pub fn unflat_c_dual(self, index: usize) -> CoreResult<(usize, usize)> {
        let len = self.mode_len(TensorMode::C)?;
        self.check_flat(index, len, "C")?;
        Ok((index / self.n.as_usize(), index % self.n.as_usize()))
    }

    fn check_index(self, name: &str, value: usize, bound: Dim) -> CoreResult<()> {
        if value < bound.as_usize() {
            Ok(())
        } else {
            Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!("index {name}={value} is outside 0..{bound}"),
            )
            .equation("§10.1"))
        }
    }

    fn check_flat(self, index: usize, len: usize, mode: &str) -> CoreResult<()> {
        if index < len {
            Ok(())
        } else {
            Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!("flat index {index} is outside mode {mode} of length {len}"),
            )
            .equation("§10.1"))
        }
    }
}

impl fmt::Display for MatMulInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "T[{},{},{}]", self.n, self.m, self.p)
    }
}

/// One of the three tensor modes (§10.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TensorMode {
    /// The `nm` mode carrying the left factor `u`.
    A = 0,
    /// The `mp` mode carrying the right factor `v`.
    B = 1,
    /// The `pn` dual-output mode carrying the factor `w`.
    C = 2,
}

impl TensorMode {
    /// All modes in canonical order.
    pub const ALL: [Self; 3] = [Self::A, Self::B, Self::C];

    /// The zero-based mode index.
    #[must_use]
    pub const fn index(self) -> usize {
        self as usize
    }

    /// The mode's short name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::A => "u",
            Self::B => "v",
            Self::C => "w",
        }
    }
}
