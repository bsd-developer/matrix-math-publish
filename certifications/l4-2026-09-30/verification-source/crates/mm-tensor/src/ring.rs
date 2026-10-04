//! Exact coefficient rings (spec §0.2, §6.6, Appendix B.7).
//!
//! Version 1 supports exactly `Z`, `Q`, `Fp` for a validated prime `p <= 2^31-1`
//! (which includes `F2`), and the Gaussian rationals `Qi`. Anything else is
//! rejected as unsupported rather than partially interpreted (§0.2).
//!
//! Arithmetic lives on a **ring context** rather than on the element type
//! because `Fp` arithmetic depends on a runtime modulus. Keeping the modulus in
//! the context rather than in every element also keeps a `Fp` coefficient one
//! `u32` wide, which matters for the Track B search state.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Debug;
use malachite::Integer;
use malachite::base::num::basic::traits::{One, Zero};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::modulus::PrimeModulus;
use mm_rat::Rat;
use mm_rat::grammar::{format_integer, parse_integer};

/// The ring discriminator used in certificate bytes (§6.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RingTag {
    /// The integers.
    Z,
    /// The rationals.
    Q,
    /// A prime field `F_p`.
    Fp,
    /// The Gaussian rationals `Q(i)`.
    Qi,
}

impl RingTag {
    /// The canonical wire string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Z => "Z",
            Self::Q => "Q",
            Self::Fp => "Fp",
            Self::Qi => "Qi",
        }
    }

    /// Parse a ring tag, rejecting anything version 1 does not support.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] for an unknown tag.
    pub fn parse(text: &str) -> CoreResult<Self> {
        match text {
            "Z" => Ok(Self::Z),
            "Q" => Ok(Self::Q),
            "Fp" => Ok(Self::Fp),
            "Qi" => Ok(Self::Qi),
            _ => Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                "version 1 supports only the ring tags Z, Q, Fp, and Qi",
            )
            .equation("§6.6")
            .value(text)),
        }
    }
}

/// An exact coefficient ring.
///
/// Every operation is exact; no implementation may round, approximate, or use a
/// floating-point intermediate (§0, §17.1).
pub trait ExactRing: Clone + Debug {
    /// The coefficient type.
    type Elem: Clone + Debug + Eq + Ord;

    /// The certificate ring tag.
    fn tag(&self) -> RingTag;

    /// The additive identity.
    fn zero(&self) -> Self::Elem;

    /// The multiplicative identity.
    fn one(&self) -> Self::Elem;

    /// Exact addition.
    fn add(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem;

    /// Exact subtraction.
    fn sub(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem;

    /// Exact multiplication.
    fn mul(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem;

    /// Exact negation.
    fn neg(&self, a: &Self::Elem) -> Self::Elem;

    /// Whether the element is the additive identity.
    fn is_zero(&self, a: &Self::Elem) -> bool;

    /// The multiplicative inverse, when it exists.
    fn inverse(&self, a: &Self::Elem) -> Option<Self::Elem>;

    /// The canonical scalar that normalizes a factor vector (§10.4).
    ///
    /// For a field this is the first nonzero coefficient, so dividing by it makes
    /// that coefficient one. For `Z` only unit scaling is permitted, so it is the
    /// sign of the first nonzero coefficient. Returns `None` for an all-zero
    /// vector, which the caller must have already rejected.
    fn normalizer(&self, factor: &[Self::Elem]) -> Option<Self::Elem>;

    /// The canonical byte encoding of one coefficient, used for term ordering
    /// and certificate bytes (§6.6, §10.4).
    fn encode(&self, a: &Self::Elem) -> String;

    /// The canonical **JSON value** for one coefficient (§6.6).
    ///
    /// This differs from [`ExactRing::encode`] exactly where the ring's wire
    /// form is a JSON string rather than a bare token: `Z` coefficients travel
    /// as normalized decimal integer *strings*, while `Fp` coefficients travel
    /// as JSON integers and `Q`/`Qi` coefficients as JSON objects. Term ordering
    /// (§10.4) uses this form, because §10.4 sorts by canonical coefficient
    /// bytes as they appear in the certificate.
    fn encode_json(&self, a: &Self::Elem) -> String {
        self.encode(a)
    }

    /// Decode one coefficient from its canonical encoding (§6.6).
    ///
    /// # Errors
    ///
    /// Returns a grammar or range rejection for malformed input.
    fn decode(&self, text: &str) -> CoreResult<Self::Elem>;

    /// Whether the encoding of `a` is already in canonical normal form.
    ///
    /// A decoder rejects a non-canonical coefficient rather than normalizing it,
    /// so that one value has exactly one certificate byte sequence (§6.3).
    fn is_canonical_encoding(&self, text: &str) -> bool {
        match self.decode(text) {
            Ok(value) => self.encode(&value) == text,
            Err(_) => false,
        }
    }

    /// Divide `factor` elementwise by `scalar`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalCoefficient`] when `scalar` is not
    /// invertible in this ring.
    fn scale_inverse(
        &self,
        factor: &[Self::Elem],
        scalar: &Self::Elem,
    ) -> CoreResult<Vec<Self::Elem>> {
        let inverse = self.inverse(scalar).ok_or_else(|| {
            CoreError::new(
                ErrorCode::NoncanonicalCoefficient,
                "the normalizing scalar is not invertible in this ring",
            )
            .equation("§10.4")
        })?;
        Ok(factor
            .iter()
            .map(|value| self.mul(value, &inverse))
            .collect())
    }

    /// Multiply `factor` elementwise by `scalar`.
    fn scale(&self, factor: &[Self::Elem], scalar: &Self::Elem) -> Vec<Self::Elem> {
        factor.iter().map(|value| self.mul(value, scalar)).collect()
    }

    /// Whether every entry of `factor` is zero (§6.6 forbids such a factor).
    fn is_zero_vector(&self, factor: &[Self::Elem]) -> bool {
        factor.iter().all(|value| self.is_zero(value))
    }
}

// ------------------------------------------------------------------------ Z

/// The ring of integers (§6.6 tag `Z`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct IntegerRing;

impl ExactRing for IntegerRing {
    type Elem = Integer;

    fn tag(&self) -> RingTag {
        RingTag::Z
    }
    fn zero(&self) -> Integer {
        Integer::ZERO
    }
    fn one(&self) -> Integer {
        Integer::ONE
    }
    fn add(&self, a: &Integer, b: &Integer) -> Integer {
        a + b
    }
    fn sub(&self, a: &Integer, b: &Integer) -> Integer {
        a - b
    }
    fn mul(&self, a: &Integer, b: &Integer) -> Integer {
        a * b
    }
    fn neg(&self, a: &Integer) -> Integer {
        -a
    }
    fn is_zero(&self, a: &Integer) -> bool {
        *a == Integer::ZERO
    }

    /// Only `1` and `-1` are units in `Z`.
    fn inverse(&self, a: &Integer) -> Option<Integer> {
        if *a == Integer::ONE {
            Some(Integer::ONE)
        } else if *a == -Integer::ONE {
            Some(-Integer::ONE)
        } else {
            None
        }
    }

    /// §10.4: for `Z` only unit scaling is used, so the normalizer is the sign
    /// of the first nonzero coefficient. Version 1 deliberately does not attempt
    /// a stronger content/gcd normalization.
    fn normalizer(&self, factor: &[Integer]) -> Option<Integer> {
        factor
            .iter()
            .find(|value| **value != Integer::ZERO)
            .map(|value| {
                if *value < Integer::ZERO {
                    -Integer::ONE
                } else {
                    Integer::ONE
                }
            })
    }

    fn encode(&self, a: &Integer) -> String {
        format_integer(a)
    }

    /// `Z` coefficients travel as normalized decimal integer strings (§6.6).
    fn encode_json(&self, a: &Integer) -> String {
        format!("\"{}\"", format_integer(a))
    }

    fn decode(&self, text: &str) -> CoreResult<Integer> {
        parse_integer(text)
    }
}

// ------------------------------------------------------------------------ Q

/// The field of rationals (§6.6 tag `Q`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RationalRing;

impl ExactRing for RationalRing {
    type Elem = Rat;

    fn tag(&self) -> RingTag {
        RingTag::Q
    }
    fn zero(&self) -> Rat {
        Rat::zero()
    }
    fn one(&self) -> Rat {
        Rat::one()
    }
    fn add(&self, a: &Rat, b: &Rat) -> Rat {
        a + b
    }
    fn sub(&self, a: &Rat, b: &Rat) -> Rat {
        a - b
    }
    fn mul(&self, a: &Rat, b: &Rat) -> Rat {
        a * b
    }
    fn neg(&self, a: &Rat) -> Rat {
        -a.clone()
    }
    fn is_zero(&self, a: &Rat) -> bool {
        a.is_zero()
    }
    fn inverse(&self, a: &Rat) -> Option<Rat> {
        a.recip().ok()
    }

    /// §10.4: divide by the first nonzero coefficient so it becomes one.
    fn normalizer(&self, factor: &[Rat]) -> Option<Rat> {
        factor.iter().find(|value| !value.is_zero()).cloned()
    }

    fn encode(&self, a: &Rat) -> String {
        a.to_canonical_json()
    }

    fn decode(&self, text: &str) -> CoreResult<Rat> {
        let (numerator, denominator) = split_rational_object(text)?;
        Rat::decode_canonical(&numerator, &denominator)
    }
}

// ----------------------------------------------------------------------- Fp

/// A prime field `F_p` (§6.6 tag `Fp`), including `F2`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimeField {
    modulus: PrimeModulus,
}

impl PrimeField {
    /// Build a field from a validated prime modulus.
    #[must_use]
    pub const fn new(modulus: PrimeModulus) -> Self {
        Self { modulus }
    }

    /// The field `F2`, the Track B baseline.
    #[must_use]
    pub const fn f2() -> Self {
        Self {
            modulus: PrimeModulus::TWO,
        }
    }

    /// The modulus.
    #[must_use]
    pub const fn modulus(self) -> PrimeModulus {
        self.modulus
    }

    fn reduce(self, value: u64) -> u32 {
        // `modulus <= 2^31-1` and every caller reduces a product of two reduced
        // values, which fits in `u64`.
        (value % self.modulus.as_u64()) as u32
    }
}

impl ExactRing for PrimeField {
    type Elem = u32;

    fn tag(&self) -> RingTag {
        RingTag::Fp
    }
    fn zero(&self) -> u32 {
        0
    }
    fn one(&self) -> u32 {
        1 % self.modulus.get()
    }
    fn add(&self, a: &u32, b: &u32) -> u32 {
        self.reduce(u64::from(*a) + u64::from(*b))
    }
    fn sub(&self, a: &u32, b: &u32) -> u32 {
        self.reduce(u64::from(*a) + self.modulus.as_u64() - u64::from(*b))
    }
    fn mul(&self, a: &u32, b: &u32) -> u32 {
        self.reduce(u64::from(*a) * u64::from(*b))
    }
    fn neg(&self, a: &u32) -> u32 {
        self.reduce(self.modulus.as_u64() - u64::from(*a))
    }
    fn is_zero(&self, a: &u32) -> bool {
        *a == 0
    }

    /// Fermat inversion is avoided in favour of the extended Euclidean algorithm
    /// so the cost does not depend on the bit length of `p`.
    fn inverse(&self, a: &u32) -> Option<u32> {
        if *a == 0 {
            return None;
        }
        let modulus = self.modulus.as_u64() as i64;
        let (mut old_r, mut r) = (i64::from(*a), modulus);
        let (mut old_s, mut s) = (1i64, 0i64);
        while r != 0 {
            let quotient = old_r / r;
            (old_r, r) = (r, old_r - quotient * r);
            (old_s, s) = (s, old_s - quotient * s);
        }
        if old_r != 1 {
            return None;
        }
        Some(old_s.rem_euclid(modulus) as u32)
    }

    /// §10.4: divide by the first nonzero coefficient. In `F2` the only nonzero
    /// element is one, so this is the identity and no scaling occurs.
    fn normalizer(&self, factor: &[u32]) -> Option<u32> {
        factor.iter().copied().find(|value| *value != 0)
    }

    fn encode(&self, a: &u32) -> String {
        format!("{a}")
    }

    /// `Fp` coefficients are JSON integers in `[0,p)` (§6.6).
    fn decode(&self, text: &str) -> CoreResult<u32> {
        if text.is_empty() || (text.len() > 1 && text.starts_with('0')) {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "an Fp coefficient is a canonical decimal integer",
            )
            .equation("§6.6")
            .value(text));
        }
        if !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "an Fp coefficient must be an unsigned decimal integer",
            )
            .equation("§6.6")
            .value(text));
        }
        let value: u32 = text.parse().map_err(|_| {
            CoreError::new(
                ErrorCode::BadRationalGrammar,
                "the Fp coefficient does not fit in the field",
            )
            .equation("§6.6")
            .value(text)
        })?;
        if value >= self.modulus.get() {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "an Fp coefficient must lie in [0,p)",
            )
            .equation("§6.6")
            .value(format!("{value} >= {}", self.modulus)));
        }
        Ok(value)
    }
}

// ----------------------------------------------------------------------- Qi

/// A Gaussian rational `a + b i` (Appendix B.7).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Gaussian {
    /// The real component.
    pub re: Rat,
    /// The imaginary component.
    pub im: Rat,
}

impl Gaussian {
    /// Build a Gaussian rational from its components.
    #[must_use]
    pub const fn new(re: Rat, im: Rat) -> Self {
        Self { re, im }
    }

    /// The squared modulus `a^2 + b^2`, used for inversion.
    #[must_use]
    pub fn norm(&self) -> Rat {
        &(&self.re * &self.re) + &(&self.im * &self.im)
    }
}

/// The field of Gaussian rationals `Q(i)` (§6.6 tag `Qi`, Appendix B.7).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GaussianRationalRing;

impl ExactRing for GaussianRationalRing {
    type Elem = Gaussian;

    fn tag(&self) -> RingTag {
        RingTag::Qi
    }
    fn zero(&self) -> Gaussian {
        Gaussian::new(Rat::zero(), Rat::zero())
    }
    fn one(&self) -> Gaussian {
        Gaussian::new(Rat::one(), Rat::zero())
    }
    fn add(&self, a: &Gaussian, b: &Gaussian) -> Gaussian {
        Gaussian::new(&a.re + &b.re, &a.im + &b.im)
    }
    fn sub(&self, a: &Gaussian, b: &Gaussian) -> Gaussian {
        Gaussian::new(&a.re - &b.re, &a.im - &b.im)
    }

    /// `(a+bi)(c+di) = (ac-bd) + (ad+bc)i` (B.7).
    fn mul(&self, a: &Gaussian, b: &Gaussian) -> Gaussian {
        Gaussian::new(
            &(&a.re * &b.re) - &(&a.im * &b.im),
            &(&a.re * &b.im) + &(&a.im * &b.re),
        )
    }
    fn neg(&self, a: &Gaussian) -> Gaussian {
        Gaussian::new(-a.re.clone(), -a.im.clone())
    }
    fn is_zero(&self, a: &Gaussian) -> bool {
        a.re.is_zero() && a.im.is_zero()
    }

    fn inverse(&self, a: &Gaussian) -> Option<Gaussian> {
        let norm = a.norm();
        if norm.is_zero() {
            return None;
        }
        let re = a.re.checked_div(&norm).ok()?;
        let im = (-a.im.clone()).checked_div(&norm).ok()?;
        Some(Gaussian::new(re, im))
    }

    fn normalizer(&self, factor: &[Gaussian]) -> Option<Gaussian> {
        factor
            .iter()
            .find(|value| !(value.re.is_zero() && value.im.is_zero()))
            .cloned()
    }

    fn encode(&self, a: &Gaussian) -> String {
        format!(
            "{{\"im\":{},\"re\":{}}}",
            a.im.to_canonical_json(),
            a.re.to_canonical_json()
        )
    }

    fn decode(&self, text: &str) -> CoreResult<Gaussian> {
        let im_text = extract_object_field(text, "im")?;
        let re_text = extract_object_field(text, "re")?;
        let (im_n, im_d) = split_rational_object(&im_text)?;
        let (re_n, re_d) = split_rational_object(&re_text)?;
        Ok(Gaussian::new(
            Rat::decode_canonical(&re_n, &re_d)?,
            Rat::decode_canonical(&im_n, &im_d)?,
        ))
    }
}

// ------------------------------------------------------------- tiny helpers

fn grammar_error(message: &str, offending: &str) -> CoreError {
    CoreError::new(
        ErrorCode::BadRationalGrammar,
        alloc::string::String::from(message),
    )
    .equation("§6.2")
    .value(offending)
}

/// Extract `{"n":"…","d":"…"}` components from a canonical rational object.
///
/// Certificate parsing proper happens in `mm-schema`; this minimal reader lets a
/// ring decode a coefficient from its already-extracted canonical text.
fn split_rational_object(text: &str) -> CoreResult<(String, String)> {
    let numerator = extract_string_field(text, "n")?;
    let denominator = extract_string_field(text, "d")?;
    Ok((numerator, denominator))
}

fn extract_string_field(text: &str, key: &str) -> CoreResult<String> {
    let needle = format!("\"{key}\":\"");
    let start = text
        .find(&needle)
        .ok_or_else(|| grammar_error("a rational object needs \"n\" and \"d\"", text))?
        + needle.len();
    let rest = text
        .get(start..)
        .ok_or_else(|| grammar_error("truncated", text))?;
    let end = rest
        .find('"')
        .ok_or_else(|| grammar_error("unterminated string", text))?;
    Ok(String::from(rest.get(..end).unwrap_or_default()))
}

fn extract_object_field(text: &str, key: &str) -> CoreResult<String> {
    let needle = format!("\"{key}\":{{");
    let start = text
        .find(&needle)
        .ok_or_else(|| grammar_error("a Gaussian needs \"re\" and \"im\"", text))?
        + needle.len()
        - 1;
    let rest = text
        .get(start..)
        .ok_or_else(|| grammar_error("truncated", text))?;
    let mut depth = 0usize;
    for (offset, ch) in rest.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(String::from(rest.get(..=offset).unwrap_or_default()));
                }
            }
            _ => {}
        }
    }
    Err(grammar_error("unbalanced object", text))
}
