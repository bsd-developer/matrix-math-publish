//! The canonical integer and rational grammar (spec §6.2, §6.4).
//!
//! The grammar is deliberately strict: a value has exactly one spelling, so a
//! certificate has exactly one canonical byte sequence and therefore exactly one
//! SHA-256 identity (§6.3). Anything that would give one number two spellings —
//! a leading `+`, a leading zero, `-0`, a non-reduced fraction, a negative
//! denominator — is rejected rather than normalized on input.

use alloc::format;
use alloc::string::String;
use malachite::Integer;
use malachite::Natural;
use malachite::base::num::conversion::traits::FromStringBase;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};

/// The maximum number of decimal digits in one numerator or denominator (§6.2).
pub const MAX_INTEGER_DIGITS: usize = 4_096;

fn bad(message: impl Into<String>, offending: &str) -> CoreError {
    CoreError::new(ErrorCode::BadRationalGrammar, message)
        .equation("§6.2")
        .value(offending)
}

/// Validate the digit-string portion of a canonical integer (§6.2).
///
/// `digits` must be nonempty, ASCII decimal only, and free of leading zeros
/// unless it is exactly `"0"`.
fn check_digits(digits: &str, whole: &str) -> CoreResult<()> {
    if digits.is_empty() {
        return Err(bad("an integer must have at least one digit", whole));
    }
    if digits.len() > MAX_INTEGER_DIGITS {
        return Err(CoreError::new(
            ErrorCode::ResourceLimit,
            format!("an integer may have at most {MAX_INTEGER_DIGITS} digits"),
        )
        .equation("§6.4")
        .value(format!("{} digits", digits.len())));
    }
    if !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(bad("integers use decimal ASCII digits only", whole));
    }
    if digits.len() > 1 && digits.starts_with('0') {
        return Err(bad("integers must not carry leading zeros", whole));
    }
    Ok(())
}

/// Parse a canonical signed integer string (§6.2).
///
/// Accepts an optional leading `-` followed by canonical digits. A leading `+`,
/// a leading zero, and `-0` are rejected.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] for a grammar violation and
/// [`ErrorCode::ResourceLimit`] when the digit count exceeds §6.4.
pub fn parse_integer(text: &str) -> CoreResult<Integer> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    if text.starts_with('+') {
        return Err(bad("a leading '+' is not canonical", text));
    }
    check_digits(digits, text)?;
    if negative && digits == "0" {
        return Err(bad("negative zero is not canonical; write \"0\"", text));
    }
    let magnitude = Natural::from_string_base(10, digits)
        .ok_or_else(|| bad("the integer digits are not parseable", text))?;
    let value = Integer::from(magnitude);
    Ok(if negative { -value } else { value })
}

/// Parse a canonical unsigned integer string, rejecting any sign (§6.2).
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] for a grammar violation.
pub fn parse_natural(text: &str) -> CoreResult<Natural> {
    if text.starts_with('-') || text.starts_with('+') {
        return Err(bad("this field must be an unsigned integer", text));
    }
    check_digits(text, text)?;
    Natural::from_string_base(10, text)
        .ok_or_else(|| bad("the integer digits are not parseable", text))
}

/// Render an integer in canonical form (§6.2).
#[must_use]
pub fn format_integer(value: &Integer) -> String {
    format!("{value}")
}

/// Render a natural number in canonical form (§6.2).
#[must_use]
pub fn format_natural(value: &Natural) -> String {
    format!("{value}")
}
