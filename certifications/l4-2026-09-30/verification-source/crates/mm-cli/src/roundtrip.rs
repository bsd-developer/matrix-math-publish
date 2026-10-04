//! Streaming byte-for-byte round-trip comparison (spec §3.5, §6.4).
//!
//! §3.5 requires the generator to re-encode the decoded typed literals and
//! require byte-for-byte equality with the published canonical bytes. Doing that
//! by materializing both sides would defeat the §6.4 streaming requirement on an
//! 8 GiB certificate, so the re-encoder writes into this comparator, which reads
//! the original in lockstep and fails at the first differing byte.

use mm_core::codes::ErrorCode;
use mm_core::error::CoreError;
use std::io::{self, Read, Write};

/// A sink that compares everything written to it against a reader.
pub struct CompareWriter<R: Read> {
    source: R,
    position: u64,
    mismatch: Option<u64>,
    buffer: Vec<u8>,
}

impl<R: Read> CompareWriter<R> {
    /// Compare subsequent writes against `source`.
    pub fn new(source: R) -> Self {
        Self {
            source,
            position: 0,
            mismatch: None,
            buffer: Vec::new(),
        }
    }

    /// Finish the comparison, checking that the source is exhausted too.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ImplementationDisagreement`] on any difference,
    /// including a source that is longer than what was written.
    pub fn finish(mut self) -> Result<(), CoreError> {
        if let Some(offset) = self.mismatch {
            return Err(round_trip_error().value(format!("first difference at byte {offset}")));
        }
        let mut tail = [0u8; 1];
        match self.source.read(&mut tail) {
            Ok(0) => Ok(()),
            Ok(_) => Err(round_trip_error().value(format!(
                "published bytes are longer than the re-encoding at {}",
                self.position
            ))),
            Err(error) => Err(CoreError::new(ErrorCode::Io, error.to_string())),
        }
    }
}

fn round_trip_error() -> CoreError {
    CoreError::new(
        ErrorCode::ImplementationDisagreement,
        "the decoded certificate does not re-encode to the published canonical bytes",
    )
    .equation("§3.5")
}

impl<R: Read> Write for CompareWriter<R> {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        if self.mismatch.is_some() {
            self.position += data.len() as u64;
            return Ok(data.len());
        }
        self.buffer.clear();
        self.buffer.resize(data.len(), 0);
        let mut filled = 0usize;
        while filled < data.len() {
            match self
                .source
                .read(self.buffer.get_mut(filled..).unwrap_or_default())
            {
                Ok(0) => break,
                Ok(read) => filled += read,
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(error),
            }
        }
        if filled < data.len() {
            // The published bytes ran out early.
            self.mismatch = Some(self.position + filled as u64);
            self.position += data.len() as u64;
            return Ok(data.len());
        }
        for (offset, (expected, actual)) in self.buffer.iter().zip(data.iter()).enumerate() {
            if expected != actual {
                self.mismatch = Some(self.position + offset as u64);
                break;
            }
        }
        self.position += data.len() as u64;
        Ok(data.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly; §17.1 governs library code"
    )]

    use super::CompareWriter;
    use std::io::Write;

    #[test]
    fn identical_streams_compare_equal() {
        let published = b"{\"a\":1}".to_vec();
        let mut writer = CompareWriter::new(published.as_slice());
        writer.write_all(b"{\"a\"").expect("write");
        writer.write_all(b":1}").expect("write");
        writer.finish().expect("streams are identical");
    }

    #[test]
    fn a_differing_byte_is_reported_with_its_offset() {
        let published = b"{\"a\":1}".to_vec();
        let mut writer = CompareWriter::new(published.as_slice());
        writer.write_all(b"{\"a\":2}").expect("write");
        let error = writer.finish().expect_err("byte 5 differs");
        assert!(
            error.values().iter().any(|value| value.contains("byte 5")),
            "{error}"
        );
    }

    #[test]
    fn a_longer_published_stream_is_reported() {
        let published = b"{\"a\":1} trailing".to_vec();
        let mut writer = CompareWriter::new(published.as_slice());
        writer.write_all(b"{\"a\":1}").expect("write");
        assert!(writer.finish().is_err(), "trailing bytes must be caught");
    }

    #[test]
    fn a_shorter_published_stream_is_reported() {
        let published = b"{\"a\"".to_vec();
        let mut writer = CompareWriter::new(published.as_slice());
        writer.write_all(b"{\"a\":1}").expect("write");
        assert!(writer.finish().is_err(), "truncation must be caught");
    }
}
