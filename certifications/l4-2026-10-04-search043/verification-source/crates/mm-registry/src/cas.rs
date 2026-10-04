//! Content-addressed storage (spec §13.6).
//!
//! Blobs are stored immutably under the SHA-256 of their **uncompressed
//! canonical** content, in `data/cas/sha256/<aa>/<bb>/<digest>`. Writes go to a
//! temporary file, are flushed, hashed, and atomically renamed, so a crash never
//! leaves a partially written blob under a valid digest name. Reads verify the
//! digest, so corruption is detected rather than propagated.

use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::hash::Sha256;
use mm_core::hex::encode_hex;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

/// A local content-addressed store rooted at a directory.
#[derive(Clone, Debug)]
pub struct Cas {
    root: PathBuf,
}

fn io(error: std::io::Error, context: &str) -> CoreError {
    CoreError::new(ErrorCode::Io, format!("{context}: {error}"))
}

impl Cas {
    /// Open (or create) a store rooted at `root`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::Io`] when the directory cannot be created.
    pub fn open(root: impl Into<PathBuf>) -> CoreResult<Self> {
        let root = root.into();
        fs::create_dir_all(&root).map_err(|error| io(error, "create CAS root"))?;
        Ok(Self { root })
    }

    /// The path a digest maps to, using two levels of fan-out (§13.6).
    #[must_use]
    pub fn path_for(&self, digest_hex: &str) -> PathBuf {
        let (aa, rest) = digest_hex.split_at(digest_hex.len().min(2));
        let (bb, _) = rest.split_at(rest.len().min(2));
        self.root.join("sha256").join(aa).join(bb).join(digest_hex)
    }

    /// Store bytes, returning the lowercase hexadecimal digest.
    ///
    /// Storing content that is already present is a no-op, so the operation is
    /// idempotent.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::Io`] on a filesystem failure.
    pub fn put(&self, data: &[u8]) -> CoreResult<String> {
        let digest = encode_hex(&mm_core::sha256(data));
        let target = self.path_for(&digest);
        if target.is_file() {
            return Ok(digest);
        }
        let parent = target
            .parent()
            .ok_or_else(|| CoreError::new(ErrorCode::Io, "CAS path has no parent"))?;
        fs::create_dir_all(parent).map_err(|error| io(error, "create CAS shard"))?;

        let temporary = parent.join(format!(".{digest}.partial"));
        {
            let mut file =
                fs::File::create(&temporary).map_err(|error| io(error, "create temporary blob"))?;
            file.write_all(data)
                .map_err(|error| io(error, "write temporary blob"))?;
            file.flush().map_err(|error| io(error, "flush blob"))?;
            file.sync_all().map_err(|error| io(error, "sync blob"))?;
        }
        fs::rename(&temporary, &target).map_err(|error| io(error, "rename blob into place"))?;
        Ok(digest)
    }

    /// Store the contents of a file.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::Io`] on a filesystem failure.
    pub fn put_file(&self, path: &Path) -> CoreResult<String> {
        let data = fs::read(path).map_err(|error| io(error, "read source file"))?;
        self.put(&data)
    }

    /// Whether a digest is present locally.
    #[must_use]
    pub fn contains(&self, digest_hex: &str) -> bool {
        self.path_for(digest_hex).is_file()
    }

    /// Retrieve bytes, verifying the digest on read (§13.6).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::DigestMismatch`] when stored bytes do not hash to
    /// their name, and [`ErrorCode::Io`] when the blob is absent.
    pub fn get(&self, digest_hex: &str) -> CoreResult<Vec<u8>> {
        let path = self.path_for(digest_hex);
        let mut file =
            fs::File::open(&path).map_err(|error| io(error, &format!("open blob {digest_hex}")))?;
        let mut data = Vec::new();
        file.read_to_end(&mut data)
            .map_err(|error| io(error, "read blob"))?;
        let actual = encode_hex(&mm_core::sha256(&data));
        if actual != digest_hex {
            return Err(CoreError::new(
                ErrorCode::DigestMismatch,
                "stored content does not hash to its content address",
            )
            .equation("§13.6")
            .value(digest_hex)
            .value(actual));
        }
        Ok(data)
    }

    /// Stream a large blob's digest without holding it in memory.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::Io`] on a read failure.
    pub fn digest_of_file(path: &Path) -> CoreResult<String> {
        let mut file = fs::File::open(path).map_err(|error| io(error, "open file"))?;
        let mut hasher = Sha256::new();
        let mut buffer = vec![0u8; 1 << 16];
        loop {
            let read = file
                .read(&mut buffer)
                .map_err(|error| io(error, "read file"))?;
            if read == 0 {
                break;
            }
            hasher.update(buffer.get(..read).unwrap_or_default());
        }
        Ok(encode_hex(&hasher.finalize()))
    }
}
