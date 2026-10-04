//! Structured, total error reporting (spec §5.4).
//!
//! Core validators are total over accepted-size input: they return a
//! [`CoreError`] rather than panicking. Every error carries a stable
//! [`ErrorCode`], an optional location, an optional normative equation
//! identifier, and optional offending exact values.

use crate::codes::ErrorCode;
use alloc::borrow::ToOwned;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt;

/// Where in the input a rejection occurred.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Location {
    /// No positional information is available.
    None,
    /// A zero-based byte offset into the canonical byte sequence.
    ByteOffset(u64),
    /// An RFC 6901 JSON pointer into the decoded document.
    JsonPointer(String),
    /// A canonical tree node identity, rendered per [`crate::path::NodePath`].
    NodePath(String),
    /// A traversal index together with its rendered `NodePath` (§5.2).
    NodeIndex {
        /// Depth-first preorder index of the node.
        index: u64,
        /// Rendered `NodePath` of the same node.
        path: String,
    },
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => f.write_str("-"),
            Self::ByteOffset(offset) => write!(f, "byte {offset}"),
            Self::JsonPointer(pointer) => write!(f, "json {pointer}"),
            Self::NodePath(path) => write!(f, "node {path}"),
            Self::NodeIndex { index, path } => write!(f, "node #{index} {path}"),
        }
    }
}

/// A structured rejection.
///
/// Construction never allocates beyond the strings the caller supplies, and the
/// type is deliberately cheap to clone so that diagnostic modes may collect
/// additional failures after the authoritative verdict is fixed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreError {
    code: ErrorCode,
    message: String,
    location: Location,
    equation: Option<&'static str>,
    values: Vec<String>,
}

impl CoreError {
    /// Create an error with a stable code and human-readable detail.
    #[must_use]
    pub fn new(code: ErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            location: Location::None,
            equation: None,
            values: Vec::new(),
        }
    }

    /// Attach a location.
    #[must_use]
    pub fn at(mut self, location: Location) -> Self {
        self.location = location;
        self
    }

    /// Attach a canonical byte offset.
    #[must_use]
    pub fn at_byte(self, offset: u64) -> Self {
        self.at(Location::ByteOffset(offset))
    }

    /// Attach a JSON pointer.
    #[must_use]
    pub fn at_pointer(self, pointer: impl Into<String>) -> Self {
        self.at(Location::JsonPointer(pointer.into()))
    }

    /// Attach the normative equation identifier this check implements.
    ///
    /// Identifiers are the Appendix labels `A1`–`A22` and `B1`–`B6`, or a
    /// section reference such as `"§6.2"`.
    #[must_use]
    pub fn equation(mut self, equation: &'static str) -> Self {
        self.equation = Some(equation);
        self
    }

    /// Attach one offending exact value, rendered in its canonical text form.
    #[must_use]
    pub fn value(mut self, value: impl Into<String>) -> Self {
        self.values.push(value.into());
        self
    }

    /// The stable rejection code.
    #[must_use]
    pub const fn code(&self) -> ErrorCode {
        self.code
    }

    /// The human-readable detail message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The recorded location, if any.
    #[must_use]
    pub const fn location(&self) -> &Location {
        &self.location
    }

    /// The recorded normative equation identifier, if any.
    #[must_use]
    pub const fn equation_id(&self) -> Option<&'static str> {
        self.equation
    }

    /// The recorded offending exact values.
    #[must_use]
    pub fn values(&self) -> &[String] {
        &self.values
    }

    /// The process exit code implied by this rejection (§9.3).
    #[must_use]
    pub const fn exit_code(&self) -> i32 {
        self.code.exit_code()
    }

    /// Render the error as canonical JSON, with lexicographically sorted keys.
    ///
    /// This is the form embedded in machine-readable verification reports.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        let mut out = String::from("{\"code\":");
        push_json_string(&mut out, self.code.as_str());
        if let Some(equation) = self.equation {
            out.push_str(",\"equation\":");
            push_json_string(&mut out, equation);
        }
        out.push_str(",\"location\":");
        match &self.location {
            Location::None => out.push_str("null"),
            Location::ByteOffset(offset) => {
                out.push_str("{\"byte_offset\":");
                out.push_str(&offset.to_string());
                out.push('}');
            }
            Location::JsonPointer(pointer) => {
                out.push_str("{\"json_pointer\":");
                push_json_string(&mut out, pointer);
                out.push('}');
            }
            Location::NodePath(path) => {
                out.push_str("{\"node_path\":");
                push_json_string(&mut out, path);
                out.push('}');
            }
            Location::NodeIndex { index, path } => {
                out.push_str("{\"node_index\":");
                out.push_str(&index.to_string());
                out.push_str(",\"node_path\":");
                push_json_string(&mut out, path);
                out.push('}');
            }
        }
        out.push_str(",\"message\":");
        push_json_string(&mut out, &self.message);
        out.push_str(",\"values\":[");
        for (index, value) in self.values.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            push_json_string(&mut out, value);
        }
        out.push_str("]}");
        out
    }
}

impl fmt::Display for CoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.code, self.message)?;
        if !matches!(self.location, Location::None) {
            write!(f, " at {}", self.location)?;
        }
        if let Some(equation) = self.equation {
            write!(f, " ({equation})")?;
        }
        for value in &self.values {
            write!(f, " value={value}")?;
        }
        Ok(())
    }
}

impl core::error::Error for CoreError {}

/// Append `value` to `out` as an RFC 8785 compatible JSON string literal.
///
/// Control characters use the shortest escape RFC 8785 permits: the two-character
/// escapes where they exist, and lowercase `\u00xx` otherwise.
pub fn push_json_string(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let mut buffer = [0u8; 6];
                let digits = b"0123456789abcdef";
                buffer[0] = b'\\';
                buffer[1] = b'u';
                buffer[2] = b'0';
                buffer[3] = b'0';
                #[allow(
                    clippy::indexing_slicing,
                    reason = "indexes are constants below the fixed buffer length"
                )]
                {
                    buffer[4] = digits[((c as usize) >> 4) & 0xf];
                    buffer[5] = digits[(c as usize) & 0xf];
                }
                out.push_str(core::str::from_utf8(&buffer).unwrap_or("\\u0000"));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Shorthand result type for core operations.
pub type CoreResult<T> = Result<T, CoreError>;

/// Convenience constructor for an unsupported-instance rejection.
#[must_use]
pub fn unsupported(message: impl Into<String>) -> CoreError {
    CoreError::new(ErrorCode::UnsupportedInstance, message)
}

/// Convenience constructor for a checked-arithmetic overflow rejection.
#[must_use]
pub fn overflow(context: &str) -> CoreError {
    CoreError::new(
        ErrorCode::ArithmeticOverflow,
        alloc::format!("checked arithmetic overflowed in {context}"),
    )
}

impl From<ErrorCode> for CoreError {
    fn from(code: ErrorCode) -> Self {
        Self::new(code, code.as_str().to_owned())
    }
}
