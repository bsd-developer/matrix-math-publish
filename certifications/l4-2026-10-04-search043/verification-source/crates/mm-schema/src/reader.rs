//! A streaming, canonicality-enforcing JSON reader (spec §6.3, §6.4).
//!
//! The reader never constructs a general-purpose in-memory JSON tree (§6.4): it
//! is a pull parser that a schema-specific decoder drives. It enforces the
//! canonical form **while** reading, so a byte sequence that is semantically
//! valid JSON but not canonical is rejected at the offending byte rather than
//! after a normalization round trip (§6.3).
//!
//! Canonical form here is RFC 8785 plus the stricter §6.2/§6.3 rules:
//!
//! - no whitespace anywhere between tokens;
//! - object keys strictly ascending in UTF-16 code-unit order, with no duplicates;
//! - strings using the shortest escape RFC 8785 permits, with lowercase `\u00xx`;
//! - numbers restricted to canonical non-negative integers, since every
//!   mathematical magnitude travels as a decimal string instead (§6.2).
//!
//! The SHA-256 of the consumed bytes is accumulated as the reader advances, so
//! the certificate identity (§6.3) needs no second pass over an 8 GiB input.

use crate::limits::{Limits, Meter};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::hash::Sha256;
use std::io::{BufRead, ErrorKind};

/// A streaming reader over canonical certificate bytes.
pub struct CanonicalReader<R: BufRead> {
    input: R,
    peeked: Option<u8>,
    meter: Meter,
    limits: Limits,
    hasher: Sha256,
    key_stack: Vec<Option<String>>,
}

impl<R: BufRead> CanonicalReader<R> {
    /// Wrap an input stream.
    pub fn new(input: R, limits: Limits) -> Self {
        Self {
            input,
            peeked: None,
            meter: Meter::new(),
            limits,
            hasher: Sha256::new(),
            key_stack: Vec::new(),
        }
    }

    /// The running resource meter, whose byte count is the current offset.
    #[must_use]
    pub const fn meter(&self) -> Meter {
        self.meter
    }

    /// The current canonical byte offset, for error locations (§5.4).
    #[must_use]
    pub const fn offset(&self) -> u64 {
        self.meter.bytes()
    }

    /// Count one decoded rational against the §6.4 ceiling.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ResourceLimit`] when the ceiling is exceeded.
    pub fn count_rational(&mut self) -> CoreResult<()> {
        self.meter.count_rational(&self.limits)
    }

    /// Finish and return the SHA-256 of every consumed byte (§6.3).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalJson`] when trailing bytes remain.
    pub fn finish(mut self) -> CoreResult<[u8; 32]> {
        if self.peek()?.is_some() {
            return Err(self.error(
                ErrorCode::NoncanonicalJson,
                "trailing bytes after the certificate document",
            ));
        }
        Ok(self.hasher.finalize())
    }

    fn error(&self, code: ErrorCode, message: &str) -> CoreError {
        CoreError::new(code, message)
            .equation("§6.3")
            .at_byte(self.meter.bytes())
    }

    fn fill(&mut self) -> CoreResult<Option<u8>> {
        if self.peeked.is_some() {
            return Ok(self.peeked);
        }
        let mut byte = [0u8; 1];
        loop {
            return match std::io::Read::read(&mut self.input, &mut byte) {
                Ok(0) => Ok(None),
                Ok(_) => {
                    self.peeked = Some(byte[0]);
                    Ok(self.peeked)
                }
                Err(error) if error.kind() == ErrorKind::Interrupted => continue,
                Err(error) => Err(CoreError::new(ErrorCode::Io, error.to_string())),
            };
        }
    }

    /// Look at the next byte without consuming it.
    ///
    /// # Errors
    ///
    /// Propagates I/O failures.
    pub fn peek(&mut self) -> CoreResult<Option<u8>> {
        self.fill()
    }

    /// Consume and return the next byte.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::InvalidJson`] at end of input.
    pub fn next_byte(&mut self) -> CoreResult<u8> {
        let byte = self
            .fill()?
            .ok_or_else(|| self.error(ErrorCode::InvalidJson, "unexpected end of input"))?;
        self.peeked = None;
        self.meter.consume_byte(&self.limits)?;
        self.hasher.update(&[byte]);
        Ok(byte)
    }

    fn expect_byte(&mut self, expected: u8) -> CoreResult<()> {
        let byte = self.next_byte()?;
        if byte == expected {
            Ok(())
        } else {
            Err(self.error(
                ErrorCode::NoncanonicalJson,
                &format!(
                    "expected {:?} but found {:?}",
                    char::from(expected),
                    char::from(byte)
                ),
            ))
        }
    }

    /// Enter an object, pushing a new key-ordering frame.
    ///
    /// # Errors
    ///
    /// Returns a rejection when the next byte is not `{` or the depth limit is hit.
    pub fn begin_object(&mut self) -> CoreResult<()> {
        self.expect_byte(b'{')?;
        self.meter.enter(&self.limits)?;
        self.key_stack.push(None);
        Ok(())
    }

    /// Read the next member key, or `None` at the end of the object.
    ///
    /// Enforces strictly ascending UTF-16 key order and rejects duplicates (§6.3).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalJson`] for a misordered or duplicate key.
    pub fn next_key(&mut self) -> CoreResult<Option<String>> {
        let first = self.key_stack.last().is_some_and(Option::is_none);
        match self.peek()? {
            Some(b'}') => {
                self.next_byte()?;
                self.meter.leave();
                self.key_stack.pop();
                return Ok(None);
            }
            Some(_) if first => {}
            Some(b',') => {
                self.next_byte()?;
            }
            _ => {
                return Err(self.error(ErrorCode::InvalidJson, "malformed object"));
            }
        }
        let key = self.read_string()?;
        if let Some(frame) = self.key_stack.last_mut() {
            if let Some(previous) = frame.as_ref()
                && !utf16_less_than(previous, &key)
            {
                let previous = previous.clone();
                return Err(self
                    .error(
                        ErrorCode::NoncanonicalJson,
                        "object keys must be strictly ascending in UTF-16 order",
                    )
                    .value(previous)
                    .value(key));
            }
            *frame = Some(key.clone());
        }
        self.expect_byte(b':')?;
        Ok(Some(key))
    }

    /// Enter an array.
    ///
    /// # Errors
    ///
    /// Returns a rejection when the next byte is not `[` or the depth limit is hit.
    pub fn begin_array(&mut self) -> CoreResult<()> {
        self.expect_byte(b'[')?;
        self.meter.enter(&self.limits)
    }

    /// Whether another array element follows, consuming the separator if so.
    ///
    /// `first` must be `true` for the first probe of each array.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::InvalidJson`] for a malformed array.
    pub fn next_element(&mut self, first: bool) -> CoreResult<bool> {
        match self.peek()? {
            Some(b']') => {
                self.next_byte()?;
                self.meter.leave();
                Ok(false)
            }
            Some(b',') if !first => {
                self.next_byte()?;
                Ok(true)
            }
            Some(_) if first => Ok(true),
            _ => Err(self.error(ErrorCode::InvalidJson, "malformed array")),
        }
    }

    /// Read a JSON string, enforcing RFC 8785 minimal escaping.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalJson`] for a non-minimal escape and
    /// [`ErrorCode::InvalidUtf8`] for malformed UTF-8.
    pub fn read_string(&mut self) -> CoreResult<String> {
        self.expect_byte(b'"')?;
        let mut bytes: Vec<u8> = Vec::new();
        loop {
            let byte = self.next_byte()?;
            match byte {
                b'"' => break,
                b'\\' => {
                    let escape = self.next_byte()?;
                    match escape {
                        b'"' => bytes.push(b'"'),
                        b'\\' => bytes.push(b'\\'),
                        b'b' => bytes.push(0x08),
                        b'f' => bytes.push(0x0c),
                        b'n' => bytes.push(b'\n'),
                        b'r' => bytes.push(b'\r'),
                        b't' => bytes.push(b'\t'),
                        b'u' => {
                            let mut digits = [0u8; 4];
                            for slot in &mut digits {
                                *slot = self.next_byte()?;
                            }
                            let code = parse_hex4(&digits).ok_or_else(|| {
                                self.error(ErrorCode::NoncanonicalJson, "malformed \\u escape")
                            })?;
                            if code >= 0x20 {
                                return Err(self.error(
                                    ErrorCode::NoncanonicalJson,
                                    "only control characters may use a \\u escape",
                                ));
                            }
                            if digits.iter().any(u8::is_ascii_uppercase) {
                                return Err(self.error(
                                    ErrorCode::NoncanonicalJson,
                                    "\\u escapes use lowercase hexadecimal",
                                ));
                            }
                            if matches!(code, 0x08 | 0x09 | 0x0a | 0x0c | 0x0d) {
                                return Err(self.error(
                                    ErrorCode::NoncanonicalJson,
                                    "this control character has a shorter canonical escape",
                                ));
                            }
                            bytes.push(code as u8);
                        }
                        other => {
                            return Err(self.error(
                                ErrorCode::NoncanonicalJson,
                                &format!("unsupported escape \\{}", char::from(other)),
                            ));
                        }
                    }
                }
                control if control < 0x20 => {
                    return Err(self.error(
                        ErrorCode::InvalidJson,
                        "an unescaped control character is not valid JSON",
                    ));
                }
                other => bytes.push(other),
            }
        }
        String::from_utf8(bytes).map_err(|_| {
            self.error(
                ErrorCode::InvalidUtf8,
                "string contents are not valid UTF-8",
            )
        })
    }

    /// Read a canonical non-negative JSON integer (§6.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalJson`] for a leading zero, sign,
    /// fraction, or exponent, and [`ErrorCode::ResourceLimit`] on overflow.
    pub fn read_u64(&mut self) -> CoreResult<u64> {
        let first = self.next_byte()?;
        if !first.is_ascii_digit() {
            return Err(self.error(
                ErrorCode::NoncanonicalJson,
                "schema integers are canonical non-negative decimals",
            ));
        }
        let mut value = u64::from(first - b'0');
        if first == b'0' {
            if self.peek()?.is_some_and(|byte| byte.is_ascii_digit()) {
                return Err(self.error(
                    ErrorCode::NoncanonicalJson,
                    "leading zeros are not canonical",
                ));
            }
        } else {
            while let Some(byte) = self.peek()? {
                if !byte.is_ascii_digit() {
                    break;
                }
                self.next_byte()?;
                value = value
                    .checked_mul(10)
                    .and_then(|scaled| scaled.checked_add(u64::from(byte - b'0')))
                    .ok_or_else(|| {
                        self.error(ErrorCode::ResourceLimit, "schema integer is out of range")
                    })?;
            }
        }
        if let Some(byte) = self.peek()?
            && matches!(byte, b'.' | b'e' | b'E')
        {
            return Err(self.error(
                ErrorCode::NoncanonicalJson,
                "schema integers carry no fraction or exponent",
            ));
        }
        Ok(value)
    }

    /// Read a `u64` and narrow it, rejecting an out-of-range value.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when the value does not fit.
    pub fn read_u16(&mut self) -> CoreResult<u16> {
        let value = self.read_u64()?;
        u16::try_from(value)
            .map_err(|_| self.error(ErrorCode::UnsupportedInstance, "value does not fit in u16"))
    }

    /// Skip one complete JSON value without materializing it.
    ///
    /// Used only to reach a deterministic first error after the authoritative
    /// verdict is fixed; the authoritative path rejects unknown fields (§6.1).
    ///
    /// # Errors
    ///
    /// Propagates malformed-input rejections.
    pub fn skip_value(&mut self) -> CoreResult<()> {
        match self.peek()? {
            Some(b'{') => {
                self.begin_object()?;
                while self.next_key()?.is_some() {
                    self.skip_value()?;
                }
                Ok(())
            }
            Some(b'[') => {
                self.begin_array()?;
                let mut first = true;
                while self.next_element(first)? {
                    self.skip_value()?;
                    first = false;
                }
                Ok(())
            }
            Some(b'"') => self.read_string().map(|_| ()),
            Some(byte) if byte.is_ascii_digit() => self.read_u64().map(|_| ()),
            _ => Err(self.error(ErrorCode::InvalidJson, "unsupported JSON value")),
        }
    }
}

/// Compare two strings by UTF-16 code units, as RFC 8785 requires.
#[must_use]
pub fn utf16_less_than(left: &str, right: &str) -> bool {
    let mut left_units = left.encode_utf16();
    let mut right_units = right.encode_utf16();
    loop {
        match (left_units.next(), right_units.next()) {
            (None, None) => return false,
            (None, Some(_)) => return true,
            (Some(_), None) => return false,
            (Some(a), Some(b)) => {
                if a != b {
                    return a < b;
                }
            }
        }
    }
}

fn parse_hex4(digits: &[u8; 4]) -> Option<u32> {
    let mut value = 0u32;
    for digit in digits {
        let nibble = match digit {
            b'0'..=b'9' => u32::from(digit - b'0'),
            b'a'..=b'f' => u32::from(digit - b'a') + 10,
            b'A'..=b'F' => u32::from(digit - b'A') + 10,
            _ => return None,
        };
        value = value * 16 + nibble;
    }
    Some(value)
}
