//! Bit-packed decomposition state over `𝔽₂` (spec §10.4, §10.6, §17.4).
//!
//! `𝔽₂` is the Track B search baseline (§1.3), and over `𝔽₂` a factor vector is
//! just a bit mask: addition is `XOR`, subtraction is addition, and a flip is two
//! `XOR`s. The largest supported mode length is `12*12 = 144` bits, so a factor
//! fits in three `u64` words.
//!
//! **Bit order is load-bearing.** Bits are stored most-significant-first —
//! coordinate `i` lives at bit `63 - (i % 64)` of word `i / 64` — so the plain
//! lexicographic comparison of the word array equals the coordinate-order
//! comparison of the bit sequence. That is exactly the §10.4 canonical term
//! order, whose keys are the canonical coefficient bytes: for `𝔽₂` those bytes
//! are one `'0'` or `'1'` per coordinate in index order, with identical
//! separators, so byte-lexicographic order and coordinate-lexicographic order
//! coincide. Storing bits the other way round would give the search a different
//! canonical order from the certificates it emits.

use mm_core::codes::ErrorCode;
use mm_core::dims::{MatMulInstance, TensorMode};
use mm_core::error::{CoreError, CoreResult};
use mm_core::hash::Sha256;

/// The largest mode length version 1 supports, `12 * 12` (§0.2).
pub const MAX_BITS: usize = 144;
/// The number of 64-bit words that holds [`MAX_BITS`] bits.
pub const WORDS: usize = MAX_BITS.div_ceil(64);

/// A bit-packed `𝔽₂` factor vector.
///
/// Ordering is lexicographic in coordinate order, matching §10.4.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F2Vec {
    words: [u64; WORDS],
}

impl F2Vec {
    /// The all-zero vector.
    pub const ZERO: Self = Self { words: [0; WORDS] };

    /// Build from an iterator of coordinate values.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::WrongVectorLength`] when the length exceeds
    /// [`MAX_BITS`].
    pub fn from_bits<I: IntoIterator<Item = bool>>(bits: I) -> CoreResult<Self> {
        let mut vector = Self::ZERO;
        for (index, bit) in bits.into_iter().enumerate() {
            if index >= MAX_BITS {
                return Err(CoreError::new(
                    ErrorCode::WrongVectorLength,
                    "an F2 factor exceeds the supported mode length",
                )
                .equation("§0.2"));
            }
            if bit {
                vector.set(index);
            }
        }
        Ok(vector)
    }

    /// Whether coordinate `index` is one.
    #[must_use]
    pub const fn get(self, index: usize) -> bool {
        if index >= MAX_BITS {
            return false;
        }
        (self.words[index / 64] >> (63 - (index % 64))) & 1 == 1
    }

    /// Set coordinate `index` to one.
    pub const fn set(&mut self, index: usize) {
        if index < MAX_BITS {
            self.words[index / 64] |= 1u64 << (63 - (index % 64));
        }
    }

    /// Whether every coordinate is zero (§6.6 forbids such a factor).
    #[must_use]
    pub fn is_zero(self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    /// The number of nonzero coordinates.
    #[must_use]
    pub fn weight(self) -> u32 {
        self.words.iter().map(|word| word.count_ones()).sum()
    }

    /// Exact addition, which over `𝔽₂` is `XOR` and equals subtraction.
    ///
    /// Exposed as `core::ops::Add` so call sites read as the field operation they
    /// are, and because `a - b` and `a + b` genuinely coincide here.
    #[must_use]
    pub fn xor(self, other: Self) -> Self {
        let mut words = [0u64; WORDS];
        for (slot, (left, right)) in words
            .iter_mut()
            .zip(self.words.iter().zip(other.words.iter()))
        {
            *slot = left ^ right;
        }
        Self { words }
    }

    /// The raw words, most-significant-coordinate first.
    #[must_use]
    pub const fn words(self) -> [u64; WORDS] {
        self.words
    }

    /// Append the canonical big-endian byte encoding used for state digests.
    pub fn write_bytes(self, out: &mut Vec<u8>) {
        for word in self.words {
            out.extend_from_slice(&word.to_be_bytes());
        }
    }

    /// The coordinates as a `bool` vector of the given length.
    #[must_use]
    pub fn to_bits(self, len: usize) -> Vec<bool> {
        (0..len).map(|index| self.get(index)).collect()
    }
}

/// One rank-one summand over `𝔽₂`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F2Term {
    /// The left factor.
    pub u: F2Vec,
    /// The right factor.
    pub v: F2Vec,
    /// The dual-output factor.
    pub w: F2Vec,
}

impl F2Term {
    /// Build a term.
    #[must_use]
    pub const fn new(u: F2Vec, v: F2Vec, w: F2Vec) -> Self {
        Self { u, v, w }
    }

    /// The factor for one tensor mode.
    #[must_use]
    pub const fn factor(self, mode: TensorMode) -> F2Vec {
        match mode {
            TensorMode::A => self.u,
            TensorMode::B => self.v,
            TensorMode::C => self.w,
        }
    }

    /// A copy with one mode's factor replaced.
    #[must_use]
    pub const fn with_factor(self, mode: TensorMode, value: F2Vec) -> Self {
        match mode {
            TensorMode::A => Self { u: value, ..self },
            TensorMode::B => Self { v: value, ..self },
            TensorMode::C => Self { w: value, ..self },
        }
    }

    /// Whether any factor is entirely zero, which makes the term vanish (§10.4).
    #[must_use]
    pub fn is_degenerate(self) -> bool {
        self.u.is_zero() || self.v.is_zero() || self.w.is_zero()
    }
}

/// A normalized decomposition state over `𝔽₂`.
///
/// The invariant is the §10.4 canonical form: no degenerate term, and terms
/// sorted by canonical coefficient bytes. Multiplicity is retained: duplicate
/// terms are not discarded, because only exact ring addition justifies a
/// reduction, and over `𝔽₂` a duplicated pair cancels rather than collapsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F2State {
    instance: MatMulInstance,
    terms: Vec<F2Term>,
}

impl F2State {
    /// Build a state and put it in canonical form.
    ///
    /// # Errors
    ///
    /// Propagates instance mode-length failures.
    pub fn new(instance: MatMulInstance, terms: Vec<F2Term>) -> CoreResult<Self> {
        let mut state = Self { instance, terms };
        state.normalize();
        let _ = state.mode_lengths()?;
        Ok(state)
    }

    /// The naive `n*m*p`-term decomposition, the standard search start point.
    ///
    /// # Errors
    ///
    /// Propagates flattening failures.
    pub fn naive(instance: MatMulInstance) -> CoreResult<Self> {
        let mut terms = Vec::new();
        for i in 0..instance.n().as_usize() {
            for k in 0..instance.m().as_usize() {
                for j in 0..instance.p().as_usize() {
                    let mut u = F2Vec::ZERO;
                    let mut v = F2Vec::ZERO;
                    let mut w = F2Vec::ZERO;
                    u.set(instance.flat_a(i, k)?);
                    v.set(instance.flat_b(k, j)?);
                    w.set(instance.flat_c_dual(j, i)?);
                    terms.push(F2Term::new(u, v, w));
                }
            }
        }
        Self::new(instance, terms)
    }

    /// The instance this state targets.
    #[must_use]
    pub const fn instance(&self) -> MatMulInstance {
        self.instance
    }

    /// The canonical term list.
    #[must_use]
    pub fn terms(&self) -> &[F2Term] {
        &self.terms
    }

    /// The current term count. This is a term count, never a rank (§10.4).
    #[must_use]
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// The three mode lengths `(nm, mp, pn)`.
    ///
    /// # Errors
    ///
    /// Propagates overflow.
    pub fn mode_lengths(&self) -> CoreResult<[usize; 3]> {
        Ok([
            self.instance.mode_len(TensorMode::A)?,
            self.instance.mode_len(TensorMode::B)?,
            self.instance.mode_len(TensorMode::C)?,
        ])
    }

    /// Put the state in §10.4 canonical form: drop degenerate terms, then sort.
    ///
    /// Over `𝔽₂` no coefficient scaling is needed, because the only nonzero
    /// element is one.
    pub fn normalize(&mut self) {
        self.terms.retain(|term| !term.is_degenerate());
        self.terms.sort_unstable();
    }

    /// Replace the term list and renormalize.
    pub fn set_terms(&mut self, terms: Vec<F2Term>) {
        self.terms = terms;
        self.normalize();
    }

    /// The canonical serialization used for state identity (§10.6).
    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.terms.len() * WORDS * 24 + 16);
        out.extend_from_slice(&(self.instance.n().get()).to_be_bytes());
        out.extend_from_slice(&(self.instance.m().get()).to_be_bytes());
        out.extend_from_slice(&(self.instance.p().get()).to_be_bytes());
        out.extend_from_slice(&(self.terms.len() as u64).to_be_bytes());
        for term in &self.terms {
            term.u.write_bytes(&mut out);
            term.v.write_bytes(&mut out);
            term.w.write_bytes(&mut out);
        }
        out
    }

    /// The 256-bit state digest used to index the transposition table (§10.6).
    ///
    /// A digest match is never sufficient on its own: §10.6 requires full
    /// canonical equality confirmation before pruning, because all fixed-size
    /// hashes collide.
    #[must_use]
    pub fn digest(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&self.canonical_bytes());
        hasher.finalize()
    }

    /// The lowercase hexadecimal state digest.
    #[must_use]
    pub fn digest_hex(&self) -> String {
        mm_core::hex::encode_hex(&self.digest())
    }

    /// Whether this state reconstructs `T_{n,m,p}` exactly over `𝔽₂` (B1).
    ///
    /// This is the incremental invariant the debug search checks after every
    /// move (§12.5), and the full reconstruction the release search checks at a
    /// configurable interval.
    ///
    /// # Errors
    ///
    /// Propagates flattening failures.
    pub fn reconstructs(&self) -> CoreResult<bool> {
        let [len_a, len_b, len_c] = self.mode_lengths()?;
        // Accumulate the whole tensor as a bitset over (a,b,c).
        let mut parity = vec![false; len_a * len_b * len_c];
        for term in &self.terms {
            for a in 0..len_a {
                if !term.u.get(a) {
                    continue;
                }
                for b in 0..len_b {
                    if !term.v.get(b) {
                        continue;
                    }
                    let base = (a * len_b + b) * len_c;
                    for c in 0..len_c {
                        if term.w.get(c)
                            && let Some(slot) = parity.get_mut(base + c)
                        {
                            *slot = !*slot;
                        }
                    }
                }
            }
        }
        for a in 0..len_a {
            let (i, k) = self.instance.unflat_a(a)?;
            for b in 0..len_b {
                let (k2, j) = self.instance.unflat_b(b)?;
                let hot = if k == k2 {
                    Some(self.instance.flat_c_dual(j, i)?)
                } else {
                    None
                };
                let base = (a * len_b + b) * len_c;
                for c in 0..len_c {
                    let expected = Some(c) == hot;
                    if parity.get(base + c).copied().unwrap_or(false) != expected {
                        return Ok(false);
                    }
                }
            }
        }
        Ok(true)
    }
}

impl core::ops::Add for F2Vec {
    type Output = Self;

    /// Addition over `𝔽₂`, which is `XOR`.
    fn add(self, other: Self) -> Self {
        self.xor(other)
    }
}

impl core::ops::Sub for F2Vec {
    type Output = Self;

    /// Subtraction over `𝔽₂`, which equals addition (Appendix B.4).
    fn sub(self, other: Self) -> Self {
        self.xor(other)
    }
}
