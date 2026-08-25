//! Stable error codes (spec §5.4).
//!
//! Every rejection returned by an authoritative path carries one of these
//! codes. Codes are part of the observable contract: they appear in CLI output,
//! JSON reports, and the invalid-fixture corpus (§6.7, §12.7). They are stable
//! identifiers, not free-form text, and MUST NOT be renamed without a spec
//! amendment.

use core::fmt;

/// A stable, machine-readable rejection code.
///
/// The string form is the canonical wire representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum ErrorCode {
    /// A value fell outside the version 1 supported domain (§0.2).
    UnsupportedInstance,
    /// A declared or implied resource limit was exceeded (§6.4).
    ResourceLimit,
    /// Bytes were not valid UTF-8.
    InvalidUtf8,
    /// Bytes were not well-formed JSON.
    InvalidJson,
    /// Bytes were valid JSON but not RFC 8785 canonical form (§6.3).
    NoncanonicalJson,
    /// A required field was absent.
    MissingField,
    /// A field of unknown name was present; unknown fields are rejected (§6.1).
    UnknownField,
    /// A field had the wrong JSON type.
    TypeMismatch,
    /// The `schema` discriminator did not match a supported certificate schema.
    SchemaMismatch,
    /// The `spec_version` did not match the version this build implements.
    SpecVersionMismatch,
    /// A recorded source hash disagreed with the locked value (§0.1).
    SourceHashMismatch,
    /// An integer or rational string violated the numeric grammar (§6.2).
    BadRationalGrammar,
    /// An array length disagreed with the count implied by the instance.
    CountMismatch,
    /// A `NodePath` was inconsistent with its instance (§5.2).
    BadPath,
    /// A distribution failed nonnegativity or normalization.
    BadSimplex,
    /// A maximum-entropy block violated an exact marginal constraint (§7.4).
    WrongMarginal,
    /// A maximum-entropy block contained a nonpositive `y` value (§7.4).
    NonpositiveY,
    /// A maximum-entropy block declared a negative `epsilon` (§7.4).
    NegativeEpsilon,
    /// A residual exceeded the declared `epsilon` (§7.4 item 4).
    InsufficientResidualBound,
    /// A directed bound was used in the wrong direction (§7.1).
    ReversedLogDirection,
    /// A claimed `omega` was negative (§7.2).
    NegativeOmega,
    /// The final Track A inequality (A21) did not hold under directed rounding.
    FeasibilityViolated,
    /// A declared field modulus was not prime (§6.6).
    CompositeModulus,
    /// A decomposition term contained an all-zero factor (§6.6).
    ZeroFactor,
    /// A factor vector had the wrong length for its tensor mode.
    WrongVectorLength,
    /// A decomposition failed to reconstruct the target tensor (B1).
    ReconstructionMismatch,
    /// Terms were not in canonical sorted order (§10.4).
    NoncanonicalTermOrder,
    /// A coefficient was not in the canonical normal form for its ring.
    NoncanonicalCoefficient,
    /// The rational repair procedure exhausted its retry budget (§7.5).
    RationalizationFailed,
    /// A content-addressed blob failed digest verification on read (§13.6).
    DigestMismatch,
    /// A configuration file was invalid (§9.5).
    BadConfig,
    /// An independent checker disagreed with the authoritative verdict (§12.6).
    ImplementationDisagreement,
    /// Arithmetic overflowed a checked width.
    ArithmeticOverflow,
    /// An input/output operation failed.
    Io,
    /// A certificate offered for the symmetric encoding is not symmetric
    /// (`docs/specs/0007_spec.md` §6): two nodes of the same level and shape
    /// carry different free variables, or an `α` varies by region.
    SymmetryViolated,
}

impl ErrorCode {
    /// The canonical wire string for this code.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedInstance => "unsupported_instance",
            Self::ResourceLimit => "resource_limit",
            Self::InvalidUtf8 => "invalid_utf8",
            Self::InvalidJson => "invalid_json",
            Self::NoncanonicalJson => "noncanonical_json",
            Self::MissingField => "missing_field",
            Self::UnknownField => "unknown_field",
            Self::TypeMismatch => "type_mismatch",
            Self::SchemaMismatch => "schema_mismatch",
            Self::SpecVersionMismatch => "spec_version_mismatch",
            Self::SourceHashMismatch => "source_hash_mismatch",
            Self::BadRationalGrammar => "bad_rational_grammar",
            Self::CountMismatch => "count_mismatch",
            Self::BadPath => "bad_path",
            Self::BadSimplex => "bad_simplex",
            Self::WrongMarginal => "wrong_marginal",
            Self::NonpositiveY => "nonpositive_y",
            Self::NegativeEpsilon => "negative_epsilon",
            Self::InsufficientResidualBound => "insufficient_residual_bound",
            Self::ReversedLogDirection => "reversed_log_direction",
            Self::NegativeOmega => "negative_omega",
            Self::FeasibilityViolated => "feasibility_violated",
            Self::CompositeModulus => "composite_modulus",
            Self::ZeroFactor => "zero_factor",
            Self::WrongVectorLength => "wrong_vector_length",
            Self::ReconstructionMismatch => "reconstruction_mismatch",
            Self::NoncanonicalTermOrder => "noncanonical_term_order",
            Self::NoncanonicalCoefficient => "noncanonical_coefficient",
            Self::RationalizationFailed => "rationalization_failed",
            Self::DigestMismatch => "digest_mismatch",
            Self::BadConfig => "bad_config",
            Self::ImplementationDisagreement => "implementation_disagreement",
            Self::ArithmeticOverflow => "arithmetic_overflow",
            Self::Io => "io",
            Self::SymmetryViolated => "symmetry_violated",
        }
    }

    /// The process exit code this rejection maps to (§9.3).
    #[must_use]
    pub const fn exit_code(self) -> i32 {
        match self {
            Self::UnsupportedInstance => 4,
            Self::ResourceLimit => 5,
            Self::ImplementationDisagreement => 6,
            Self::BadConfig => 2,
            Self::Io => 2,
            // A rejection, like every other certificate-content failure (§9.3).
            Self::SymmetryViolated => 3,
            _ => 3,
        }
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
