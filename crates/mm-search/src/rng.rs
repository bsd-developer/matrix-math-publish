//! Deterministic stochastic search RNG (spec §8.3, §10.8, §13.3).
//!
//! §8.3 fixes ChaCha20 with an explicitly recorded algorithm version for
//! stochastic CPU search, and §13.3 requires explicit RNG state with no ambient
//! randomness and no wall-clock-dependent decisions. This is a direct
//! transcription of the RFC 8439 block function, checked against the RFC's own
//! test vectors, so a run is reproducible from its recorded seed alone (replay
//! level R2, §12.3).

use mm_core::hash::Sha256;

/// The recorded algorithm version for the search RNG (§8.3).
///
/// It appears in run records and witnesses. Changing the stream in any way
/// requires bumping this string, because an old seed would otherwise silently
/// replay to a different trajectory.
pub const RNG_ALGORITHM: &str = "chacha20-rfc8439/1";

/// The domain separator used to derive per-worker seeds (§10.8).
pub const WORKER_SEED_DOMAIN: &[u8] = b"matrix-math-worker-v1";

/// A 256-bit seed.
pub type Seed256 = [u8; 32];

/// Derive a worker's seed as `SHA-256(domain || master_seed || worker_id)` (§10.8).
///
/// The worker id is appended in big-endian so the derivation is independent of
/// host byte order.
#[must_use]
pub fn derive_worker_seed(master: Seed256, worker: u32) -> Seed256 {
    let mut hasher = Sha256::new();
    hasher.update(WORKER_SEED_DOMAIN);
    hasher.update(&master);
    hasher.update(&worker.to_be_bytes());
    hasher.finalize()
}

/// A ChaCha20 stream cipher used as a deterministic random number generator.
#[derive(Clone, Debug)]
pub struct ChaCha20Rng {
    state: [u32; 16],
    buffer: [u32; 16],
    used: usize,
}

const CONSTANTS: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];

#[inline]
fn quarter_round(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = (state[d] ^ state[a]).rotate_left(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_left(12);
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = (state[d] ^ state[a]).rotate_left(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_left(7);
}

impl ChaCha20Rng {
    /// Create a generator from a 256-bit seed, with a zero nonce and counter.
    #[must_use]
    pub fn from_seed(seed: Seed256) -> Self {
        Self::with_nonce(seed, [0u8; 12], 0)
    }

    /// Create a generator with an explicit nonce and block counter.
    ///
    /// Restarts use a distinct counter rather than a re-seeded generator, so a
    /// walk's whole trajectory is a function of `(seed, restart index, step)`.
    #[must_use]
    pub fn with_nonce(seed: Seed256, nonce: [u8; 12], counter: u32) -> Self {
        let mut state = [0u32; 16];
        state[0..4].copy_from_slice(&CONSTANTS);
        for index in 0..8 {
            let base = index * 4;
            state[4 + index] =
                u32::from_le_bytes([seed[base], seed[base + 1], seed[base + 2], seed[base + 3]]);
        }
        state[12] = counter;
        for index in 0..3 {
            let base = index * 4;
            state[13 + index] = u32::from_le_bytes([
                nonce[base],
                nonce[base + 1],
                nonce[base + 2],
                nonce[base + 3],
            ]);
        }
        Self {
            state,
            buffer: [0u32; 16],
            used: 16,
        }
    }

    /// The current block counter, which is part of the replayable RNG state.
    #[must_use]
    pub const fn counter(&self) -> u32 {
        self.state[12]
    }

    fn refill(&mut self) {
        let mut working = self.state;
        for _ in 0..10 {
            quarter_round(&mut working, 0, 4, 8, 12);
            quarter_round(&mut working, 1, 5, 9, 13);
            quarter_round(&mut working, 2, 6, 10, 14);
            quarter_round(&mut working, 3, 7, 11, 15);
            quarter_round(&mut working, 0, 5, 10, 15);
            quarter_round(&mut working, 1, 6, 11, 12);
            quarter_round(&mut working, 2, 7, 8, 13);
            quarter_round(&mut working, 3, 4, 9, 14);
        }
        for (slot, (mixed, original)) in self
            .buffer
            .iter_mut()
            .zip(working.iter().zip(self.state.iter()))
        {
            *slot = mixed.wrapping_add(*original);
        }
        self.state[12] = self.state[12].wrapping_add(1);
        self.used = 0;
    }

    /// The next 32 bits of the stream.
    pub fn next_u32(&mut self) -> u32 {
        if self.used == 16 {
            self.refill();
        }
        let value = self.buffer[self.used];
        self.used += 1;
        value
    }

    /// The next 64 bits of the stream.
    pub fn next_u64(&mut self) -> u64 {
        let low = u64::from(self.next_u32());
        let high = u64::from(self.next_u32());
        (high << 32) | low
    }

    /// A uniform value in `0..bound`, rejecting to remove modulo bias.
    ///
    /// Rejection keeps the distribution exactly uniform, which matters because
    /// §10.8's baseline is *uniform* random selection over valid flips and H6
    /// measures learned guidance against it.
    pub fn below(&mut self, bound: u64) -> u64 {
        if bound <= 1 {
            return 0;
        }
        let zone = u64::MAX - (u64::MAX % bound);
        loop {
            let candidate = self.next_u64();
            if candidate < zone {
                return candidate % bound;
            }
        }
    }

    /// The raw ChaCha20 block for one counter value, used by the RFC test vectors.
    #[must_use]
    pub fn block(seed: Seed256, nonce: [u8; 12], counter: u32) -> [u32; 16] {
        let mut generator = Self::with_nonce(seed, nonce, counter);
        generator.refill();
        generator.buffer
    }
}
