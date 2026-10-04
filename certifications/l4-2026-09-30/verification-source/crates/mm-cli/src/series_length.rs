//! `mm series-length` — the §7.3 series length one precision selects.
//!
//! `docs/specs/0002_spec.md` §4.2 requires the differential harness to obtain
//! the Rust value from `crates/mm-rat` rather than from a table, so that a
//! transcription slip in one implementation is caught instead of agreed upon.
//! This subcommand is that entry point: it takes a rational `z` as an exact
//! numerator and denominator in the §6.2 canonical grammar, plus a precision,
//! and prints the selected length.
//!
//! It computes nothing itself. `mm_rat::log2::series_length` is the definition.

use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_rat::log2::{Precision, series_length};
use mm_rat::rational::Rat;

/// Exit code for a successful run (§9.3).
const EXIT_OK: u8 = 0;

fn usage_error(detail: &str) -> CoreError {
    CoreError::new(ErrorCode::UnsupportedInstance, detail.to_string())
        .equation("§9.3")
        .value("mm series-length <numerator> <denominator> <precision>".to_string())
}

/// Print `seriesLength(numerator/denominator, precision)` (`0002_spec.md` L3).
///
/// # Errors
///
/// Returns a usage error for a malformed argument list, and propagates the
/// domain and cap failures of [`series_length`].
pub fn run(arguments: &[String]) -> CoreResult<u8> {
    let [numerator, denominator, precision] = arguments else {
        return Err(usage_error("series-length takes exactly three arguments"));
    };
    let precision: u32 = precision
        .parse()
        .map_err(|_| usage_error("the precision must be a decimal integer"))?;
    // `decode_canonical` is the §6.2 grammar reader, so a vector whose rational
    // is not canonical is rejected here rather than silently coerced.
    let z = Rat::decode_canonical(numerator, denominator)?;
    println!("{}", series_length(&z, Precision::new(precision)?)?);
    Ok(EXIT_OK)
}
