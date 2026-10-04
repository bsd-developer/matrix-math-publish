//! Streaming resource limits (spec §6.4).
//!
//! Limits are checked **incrementally**, as bytes and values arrive, so a
//! hostile input is rejected before it can allocate. Exceeding any limit
//! produces the stable `resource_limit` rejection.

use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};

/// The default canonical uncompressed byte ceiling, 8 GiB (§6.4).
pub const DEFAULT_MAX_BYTES: u64 = 8 * 1024 * 1024 * 1024;
/// The default rational-value ceiling, 50,000,000 (§6.4).
pub const DEFAULT_MAX_RATIONALS: u64 = 50_000_000;
/// The default nesting-depth ceiling, 32 (§6.4).
pub const DEFAULT_MAX_DEPTH: u32 = 32;

/// The resource envelope a decode runs under (§6.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Maximum canonical uncompressed bytes.
    pub max_bytes: u64,
    /// Maximum number of rational values.
    pub max_rationals: u64,
    /// Maximum JSON nesting depth.
    pub max_depth: u32,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_bytes: DEFAULT_MAX_BYTES,
            max_rationals: DEFAULT_MAX_RATIONALS,
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }
}

impl Limits {
    /// A tighter envelope for tests and small fixtures.
    #[must_use]
    pub const fn small() -> Self {
        Self {
            max_bytes: 64 * 1024 * 1024,
            max_rationals: 1_000_000,
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }
}

/// Running counters checked against [`Limits`] during a decode.
#[derive(Clone, Copy, Debug, Default)]
pub struct Meter {
    bytes: u64,
    rationals: u64,
    depth: u32,
}

impl Meter {
    /// Start a fresh meter.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bytes: 0,
            rationals: 0,
            depth: 0,
        }
    }

    /// Bytes consumed so far, which is also the current canonical byte offset.
    #[must_use]
    pub const fn bytes(self) -> u64 {
        self.bytes
    }

    /// Rational values decoded so far.
    #[must_use]
    pub const fn rationals(self) -> u64 {
        self.rationals
    }

    /// The current nesting depth.
    #[must_use]
    pub const fn depth(self) -> u32 {
        self.depth
    }

    /// Account for one consumed byte.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ResourceLimit`] when the byte ceiling is exceeded.
    pub fn consume_byte(&mut self, limits: &Limits) -> CoreResult<()> {
        self.bytes += 1;
        if self.bytes > limits.max_bytes {
            return Err(limit("canonical byte limit exceeded", self.bytes));
        }
        Ok(())
    }

    /// Account for one decoded rational value.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ResourceLimit`] when the rational ceiling is exceeded.
    pub fn count_rational(&mut self, limits: &Limits) -> CoreResult<()> {
        self.rationals += 1;
        if self.rationals > limits.max_rationals {
            return Err(limit("rational value limit exceeded", self.rationals));
        }
        Ok(())
    }

    /// Enter one nesting level.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ResourceLimit`] when the depth ceiling is exceeded.
    pub fn enter(&mut self, limits: &Limits) -> CoreResult<()> {
        self.depth += 1;
        if self.depth > limits.max_depth {
            return Err(limit("nesting depth limit exceeded", u64::from(self.depth)));
        }
        Ok(())
    }

    /// Leave one nesting level.
    pub fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }
}

fn limit(message: &str, observed: u64) -> CoreError {
    CoreError::new(ErrorCode::ResourceLimit, message)
        .equation("§6.4")
        .value(alloc_format(observed))
}

fn alloc_format(value: u64) -> String {
    format!("{value}")
}
