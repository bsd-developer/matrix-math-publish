//! Canonical JSON writing (spec §6.3).
//!
//! The writer is intentionally low-level: callers emit members in sorted order
//! and the writer *checks* that they did. Producing bytes that the reader would
//! reject is then a caught defect rather than a certificate whose digest nobody
//! can reproduce.

use crate::reader::utf16_less_than;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult, push_json_string};
use mm_core::hash::Sha256;
use std::io::Write;

/// One open container.
///
/// A single stack rather than two is what keeps `separate` honest: an object
/// nested inside an array must not take the array's separator for its own
/// members, and two independent stacks cannot express that.
enum Frame {
    /// An open object, holding the previous key for the §6.3 order check.
    Object(Option<String>),
    /// An open array, holding whether the next element is the first.
    Array(bool),
}

/// A canonical JSON writer that hashes as it emits.
pub struct CanonicalWriter<W: Write> {
    output: W,
    hasher: Sha256,
    bytes: u64,
    frames: Vec<Frame>,
}

impl<W: Write> CanonicalWriter<W> {
    /// Wrap an output stream.
    pub fn new(output: W) -> Self {
        Self {
            output,
            hasher: Sha256::new(),
            bytes: 0,
            frames: Vec::new(),
        }
    }

    /// Total bytes written.
    #[must_use]
    pub const fn byte_count(&self) -> u64 {
        self.bytes
    }

    /// Finish and return the SHA-256 of the emitted canonical bytes (§6.3).
    ///
    /// # Errors
    ///
    /// Propagates flush failures.
    pub fn finish(mut self) -> CoreResult<[u8; 32]> {
        self.output
            .flush()
            .map_err(|error| CoreError::new(ErrorCode::Io, error.to_string()))?;
        Ok(self.hasher.finalize())
    }

    fn raw(&mut self, text: &str) -> CoreResult<()> {
        self.output
            .write_all(text.as_bytes())
            .map_err(|error| CoreError::new(ErrorCode::Io, error.to_string()))?;
        self.hasher.update(text.as_bytes());
        self.bytes += text.len() as u64;
        Ok(())
    }

    /// Begin an object.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn begin_object(&mut self) -> CoreResult<()> {
        self.separate()?;
        self.raw("{")?;
        self.frames.push(Frame::Object(None));
        Ok(())
    }

    /// End an object.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn end_object(&mut self) -> CoreResult<()> {
        self.frames.pop();
        self.raw("}")
    }

    /// Emit a member key, checking strictly ascending UTF-16 order (§6.3).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalJson`] when the key is out of order.
    pub fn key(&mut self, name: &str) -> CoreResult<()> {
        let needs_comma = match self.frames.last() {
            Some(Frame::Object(Some(previous))) => {
                if !utf16_less_than(previous, name) {
                    return Err(CoreError::new(
                        ErrorCode::NoncanonicalJson,
                        "object keys must be emitted in strictly ascending UTF-16 order",
                    )
                    .equation("§6.3")
                    .value(previous.clone())
                    .value(name));
                }
                true
            }
            _ => false,
        };
        if needs_comma {
            self.raw(",")?;
        }
        let mut encoded = String::new();
        push_json_string(&mut encoded, name);
        self.raw(&encoded)?;
        self.raw(":")?;
        if let Some(Frame::Object(previous)) = self.frames.last_mut() {
            *previous = Some(name.to_owned());
        }
        Ok(())
    }

    /// Begin an array.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn begin_array(&mut self) -> CoreResult<()> {
        self.separate()?;
        self.raw("[")?;
        self.frames.push(Frame::Array(true));
        Ok(())
    }

    /// End an array.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn end_array(&mut self) -> CoreResult<()> {
        self.frames.pop();
        self.raw("]")
    }

    /// Emit a string value.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn string(&mut self, value: &str) -> CoreResult<()> {
        self.separate()?;
        let mut encoded = String::new();
        push_json_string(&mut encoded, value);
        self.raw(&encoded)
    }

    /// Emit a non-negative integer value.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn integer(&mut self, value: u64) -> CoreResult<()> {
        self.separate()?;
        self.raw(&value.to_string())
    }

    /// Emit already-canonical raw JSON, such as a preformatted rational object.
    ///
    /// # Errors
    ///
    /// Propagates write failures.
    pub fn raw_value(&mut self, json: &str) -> CoreResult<()> {
        self.separate()?;
        self.raw(json)
    }

    /// Insert an array element separator when one is due.
    ///
    /// Only the **innermost** container decides. Inside an object the preceding
    /// `key` already emitted any comma, so a value there must not add one.
    fn separate(&mut self) -> CoreResult<()> {
        match self.frames.last_mut() {
            Some(Frame::Array(first)) => {
                if *first {
                    *first = false;
                    Ok(())
                } else {
                    self.raw(",")
                }
            }
            _ => Ok(()),
        }
    }
}
