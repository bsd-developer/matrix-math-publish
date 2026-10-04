//! Lowercase hexadecimal encoding (spec §8.3).

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult};
use alloc::string::String;

/// Encode bytes as lowercase hexadecimal.
#[must_use]
pub fn encode_hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        let hi = usize::from(byte >> 4);
        let lo = usize::from(byte & 0x0f);
        out.push(char::from(DIGITS[hi]));
        out.push(char::from(DIGITS[lo]));
    }
    out
}

/// Decode exactly 64 lowercase hexadecimal characters into a 32-byte digest.
///
/// Uppercase input is rejected: §8.3 fixes lowercase as the canonical form, and
/// silently accepting both would let one digest have two spellings.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] when the length is wrong or a
/// character is not a lowercase hexadecimal digit.
pub fn decode_hex32(text: &str) -> CoreResult<[u8; 32]> {
    let bytes = text.as_bytes();
    if bytes.len() != 64 {
        return Err(CoreError::new(
            ErrorCode::BadRationalGrammar,
            "a SHA-256 digest must be exactly 64 lowercase hexadecimal characters",
        )
        .value(text));
    }
    let mut out = [0u8; 32];
    for (index, chunk) in bytes.chunks_exact(2).enumerate() {
        let hi = nibble(chunk[0])?;
        let lo = nibble(chunk[1])?;
        out[index] = (hi << 4) | lo;
    }
    Ok(out)
}

fn nibble(byte: u8) -> CoreResult<u8> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(CoreError::new(
            ErrorCode::BadRationalGrammar,
            "digest characters must be lowercase hexadecimal",
        )),
    }
}
