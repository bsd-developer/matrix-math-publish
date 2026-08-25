//! Grammar, directed-bound, logarithm, and entropy conformance tests
//! (spec §6.2, §7.1–§7.4, §7.6).

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::ErrorCode;
use mm_rat::bounds::{Interval, LowerBound, UpperBound};
use mm_rat::entropy::{
    entropy_enclosure, max_entropy_upper, term_enclosure, validate_positive_simplex,
    validate_simplex, weighted_conditional_entropy,
};
use mm_rat::grammar::{parse_integer, parse_natural};
use mm_rat::log2::{
    MAX_PRECISION_BITS, MIN_PRECISION_BITS, Precision, SERIES_LENGTH_CAP, artanh_enclosure,
    inv_ln2_enclosure, ln2_enclosure, log2_enclosure, normalize, series_length,
    series_length_for_target,
};
use mm_rat::rational::Rat;

fn precision(bits: u32) -> Precision {
    Precision::new(bits).expect("supported precision")
}

/// Parse a decimal literal such as `"1.58496250072115618145"` exactly as a rational.
fn decimal(text: &str) -> Rat {
    let (sign, body) = match text.strip_prefix('-') {
        Some(rest) => (-1i64, rest),
        None => (1i64, text),
    };
    let (whole, fraction) = body.split_once('.').unwrap_or((body, ""));
    let joined = format!("{whole}{fraction}");
    let trimmed = joined.trim_start_matches('0');
    let digits = if trimmed.is_empty() { "0" } else { trimmed };
    let numerator = parse_integer(digits).expect("digits parse");
    let mut value = Rat::from(&numerator);
    for _ in 0..fraction.len() {
        value = value.checked_div(&Rat::from_integer(10)).expect("nonzero");
    }
    if sign < 0 { -value } else { value }
}

// ---------------------------------------------------------------- grammar §6.2

#[test]
fn canonical_integer_grammar_accepts_only_one_spelling() {
    assert_eq!(format!("{}", parse_integer("0").expect("zero")), "0");
    assert_eq!(format!("{}", parse_integer("-3").expect("neg")), "-3");
    assert_eq!(
        format!("{}", parse_integer("1234567890").expect("big")),
        "1234567890"
    );

    for bad in [
        "+1", "01", "-0", "", "1.0", "1e3", " 1", "1 ", "０", "-01", "0x10",
    ] {
        assert_eq!(
            parse_integer(bad)
                .expect_err(&format!("{bad:?} must reject"))
                .code(),
            ErrorCode::BadRationalGrammar,
            "input {bad:?}"
        );
    }
    for bad in ["-1", "+1"] {
        assert!(parse_natural(bad).is_err(), "signed natural {bad:?}");
    }
}

#[test]
fn integers_beyond_the_digit_limit_hit_the_resource_limit() {
    let long = "1".repeat(4_097);
    assert_eq!(
        parse_integer(&long).expect_err("too long").code(),
        ErrorCode::ResourceLimit
    );
    let ok = "1".repeat(4_096);
    assert!(parse_integer(&ok).is_ok());
}

#[test]
fn canonical_rational_pairs_round_trip() {
    let value = Rat::decode_canonical("-3", "7").expect("valid");
    assert_eq!(value.numerator_text(), "-3");
    assert_eq!(value.denominator_text(), "7");
    assert_eq!(value.to_canonical_json(), "{\"d\":\"7\",\"n\":\"-3\"}");

    let zero = Rat::decode_canonical("0", "1").expect("valid zero");
    assert!(zero.is_zero());
    assert_eq!(zero.to_canonical_json(), "{\"d\":\"1\",\"n\":\"0\"}");
}

#[test]
fn noncanonical_rational_pairs_reject() {
    // Not in lowest terms.
    assert_eq!(
        Rat::decode_canonical("2", "4")
            .expect_err("reducible")
            .code(),
        ErrorCode::BadRationalGrammar
    );
    // Zero with a denominator other than one.
    assert_eq!(
        Rat::decode_canonical("0", "5")
            .expect_err("bad zero")
            .code(),
        ErrorCode::BadRationalGrammar
    );
    // Zero denominator.
    assert_eq!(
        Rat::decode_canonical("1", "0")
            .expect_err("zero den")
            .code(),
        ErrorCode::BadRationalGrammar
    );
    // Signed denominator.
    assert!(Rat::decode_canonical("1", "-2").is_err());
    // Leading zeros.
    assert!(Rat::decode_canonical("01", "2").is_err());
    assert!(Rat::decode_canonical("1", "02").is_err());
}

// ------------------------------------------------------- directed bounds §7.1

#[test]
fn interval_requires_ordered_endpoints() {
    let lo = LowerBound::assert(Rat::from_integer(3));
    let hi = UpperBound::assert(Rat::from_integer(2));
    assert_eq!(
        Interval::new(lo, hi).expect_err("reversed").code(),
        ErrorCode::ReversedLogDirection
    );
}

#[test]
fn nonnegative_scaling_rejects_a_signed_multiplier() {
    let lower = LowerBound::assert(Rat::from_integer(5));
    assert_eq!(
        lower
            .scale_nonnegative(&Rat::from_integer(-1))
            .expect_err("signed multiplier")
            .code(),
        ErrorCode::ReversedLogDirection
    );
    assert!(lower.scale_nonnegative(&Rat::from_integer(2)).is_ok());
}

/// §14.7 step 1: interval multiplication must be sign-aware, not monotonic.
#[test]
fn interval_multiplication_is_sign_aware() {
    let straddling = Interval::new(
        LowerBound::assert(Rat::from_integer(-2)),
        UpperBound::assert(Rat::from_integer(3)),
    )
    .expect("ordered");
    let other = Interval::new(
        LowerBound::assert(Rat::from_integer(-5)),
        UpperBound::assert(Rat::from_integer(7)),
    )
    .expect("ordered");
    let product = straddling.mul(&other);
    // Endpoint products are 10, -14, -15, and 21; the extremes are -15 and 21.
    assert_eq!(*product.lower().value(), Rat::from_integer(-15));
    assert_eq!(*product.upper().value(), Rat::from_integer(21));

    // Brute-force check on a grid of interior points.
    for a in -2..=3 {
        for b in -5..=7 {
            let point = Rat::from_integer(a * b);
            assert!(product.contains(&point), "{a}*{b} escaped {product}");
        }
    }
}

// -------------------------------------------------------------- log2 §7.3

#[test]
fn normalization_is_exact() {
    for (num, den, expected_exponent) in [
        (1i64, 1i64, 0i64),
        (2, 1, 1),
        (8, 1, 3),
        (1, 8, -3),
        (3, 1, 1),
        (3, 4, -1),
        (1000, 1, 9),
    ] {
        let value = Rat::from_signeds(num, den);
        let normalized = normalize(&value).expect("positive");
        assert_eq!(normalized.exponent, expected_exponent, "{num}/{den}");
        assert!(normalized.mantissa >= Rat::one());
        assert!(normalized.mantissa < Rat::from_integer(2));
        let rebuilt =
            &normalized.mantissa * &Rat::from_integer(2).pow(normalized.exponent).expect("pow");
        assert_eq!(rebuilt, value, "{num}/{den} reconstruction");
    }
}

#[test]
fn log2_rejects_nonpositive_input() {
    for value in [Rat::zero(), Rat::from_integer(-1), Rat::from_signeds(-1, 3)] {
        assert_eq!(
            log2_enclosure(&value, precision(64))
                .expect_err("nonpositive")
                .code(),
            ErrorCode::BadRationalGrammar
        );
    }
}

/// Powers of two must be enclosed exactly: the interval is a point (§7.3).
#[test]
fn log2_of_powers_of_two_is_exact() {
    for exponent in -20i64..=20 {
        let value = Rat::from_integer(2).pow(exponent).expect("pow");
        let enclosure = log2_enclosure(&value, precision(64)).expect("positive");
        assert!(enclosure.width().is_zero(), "2^{exponent} was not exact");
        assert_eq!(
            *enclosure.lower().value(),
            Rat::from_integer(exponent),
            "2^{exponent}"
        );
    }
}

/// Independent reference values computed with Python's arbitrary-precision
/// `decimal` module at 90 significant digits (§12.6 differential vectors).
#[test]
fn log2_encloses_independent_reference_values() {
    let cases: [(i64, i64, &str); 6] = [
        (
            3,
            1,
            "1.5849625007211561814537389439478165087598144076924810604557526545410982277943585625222804749180882420909806624750591673437175524410609248221420839506216982994936575922385852344415825363027476853069780516875995",
        ),
        (
            10,
            1,
            "3.3219280948873623478703194294893901758648313930245806120547563958159347766086252158501397433593701550996573717102502518268240969842635268882753027729986553938519513526575055686430176091900248916669414333740119",
        ),
        (
            7,
            5,
            "0.4854268271702417595716498877424406327761952329415601716225353282543860722535677706477212558108406300077031301790753212191492580347109088956732429244230039731820848710537273243961552307005081629296175540544085",
        ),
        (
            1,
            3,
            "-1.584962500721156181453738943947816508759814407692481060455752654541098227794358562522280474918088242090980662475059167343717552441060924822142083950621698299493657592238585234441582536302747685306978051687599",
        ),
        (
            22,
            7,
            "1.6520766965796931487573937294939621500622048997156272876355099216560097708578253662116303001166897036279076983744454325997201983437067464132620661074698306866598367543825856090195232010942946737554721673329167",
        ),
        (
            1000003,
            999983,
            "0.0000288541027974606605311009967466702872434102026936390949018603467640861901772873617749776705271305360507231125445296100538251087039365111636535233999509707185942265547702345951591221527808480302153597367538",
        ),
    ];
    for (num, den, reference_text) in cases {
        let value = Rat::from_signeds(num, den);
        let reference = decimal(reference_text);
        for bits in [32u32, 64, 128, 256] {
            let enclosure = log2_enclosure(&value, precision(bits)).expect("positive");
            assert!(
                enclosure.contains(&reference),
                "log2({num}/{den}) at {bits} bits: {enclosure} excludes reference"
            );
            let tolerance = precision(bits).tolerance().expect("tolerance");
            assert!(
                enclosure.width() <= tolerance,
                "log2({num}/{den}) at {bits} bits: width {} exceeds 2^-{bits}",
                enclosure.width()
            );
        }
    }
}

#[test]
fn ln2_and_its_reciprocal_enclose_reference_values() {
    let tolerance = Rat::from_integer(2).pow(-80).expect("pow");
    let ln2_reference = decimal(
        "0.6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186875420014810205706857336855202357581305570326707516350759619307275708283714351903070386238916734711233501153644",
    );
    let inv_reference = decimal(
        "1.4426950408889634073599246810018921374266459541529859341354494069311092191811850798855266228935063444969975183096525442555931016871683596427206621582234793362745373698847184936307013876635320155338943189166648",
    );
    let ln2 = ln2_enclosure(&tolerance).expect("series");
    assert!(ln2.contains(&ln2_reference), "ln2 {ln2}");
    let inv = inv_ln2_enclosure(&tolerance).expect("series");
    assert!(inv.contains(&inv_reference), "1/ln2 {inv}");
}

#[test]
fn log2_is_monotone_on_a_sampled_grid() {
    let bits = precision(64);
    let mut previous: Option<Rat> = None;
    for numerator in 1..=40i64 {
        let value = Rat::from_signeds(numerator, 7);
        let enclosure = log2_enclosure(&value, bits).expect("positive");
        if let Some(previous_upper) = &previous {
            assert!(
                enclosure.upper().value() >= previous_upper,
                "log2 lost monotonicity at {numerator}/7"
            );
        }
        previous = Some(enclosure.upper().value().clone());
    }
}

/// `log2(a) + log2(b)` and `log2(a*b)` must have overlapping enclosures.
#[test]
fn log2_is_additive_within_the_enclosures() {
    let bits = precision(96);
    for (a_num, b_num) in [(3i64, 5i64), (7, 11), (2, 9), (13, 17)] {
        let a = Rat::from_signeds(a_num, 4);
        let b = Rat::from_signeds(b_num, 3);
        let sum = log2_enclosure(&a, bits)
            .expect("positive")
            .add(&log2_enclosure(&b, bits).expect("positive"));
        let product = log2_enclosure(&(&a * &b), bits).expect("positive");
        assert!(
            sum.lower().value() <= product.upper().value()
                && product.lower().value() <= sum.upper().value(),
            "log2 additivity failed for {a_num}/4 * {b_num}/3: {sum} vs {product}"
        );
    }
}

#[test]
fn precision_range_is_enforced() {
    assert!(Precision::new(MIN_PRECISION_BITS).is_ok());
    assert!(Precision::new(MAX_PRECISION_BITS).is_ok());
    for bits in [0u32, 31, 4_097, 100_000] {
        assert_eq!(
            Precision::new(bits).expect_err("out of range").code(),
            ErrorCode::UnsupportedInstance
        );
    }
}

// ----------------------------------------------------------- entropy §7.3–§7.6

#[test]
fn simplex_validation_is_exact() {
    let good = [
        Rat::from_signeds(1, 2),
        Rat::from_signeds(1, 3),
        Rat::from_signeds(1, 6),
    ];
    assert!(validate_simplex(&good).is_ok());
    assert!(validate_positive_simplex(&good).is_ok());

    let with_zero = [
        Rat::from_signeds(1, 2),
        Rat::from_signeds(1, 2),
        Rat::zero(),
    ];
    assert!(validate_simplex(&with_zero).is_ok());
    assert_eq!(
        validate_positive_simplex(&with_zero)
            .expect_err("zero entry")
            .code(),
        ErrorCode::NonpositiveY
    );

    let negative = [Rat::from_signeds(3, 2), Rat::from_signeds(-1, 2)];
    assert_eq!(
        validate_simplex(&negative).expect_err("negative").code(),
        ErrorCode::BadSimplex
    );

    // Sums to 999999/1000000, not one: must reject rather than tolerate.
    let near_one = [Rat::from_signeds(999_999, 1_000_000)];
    assert_eq!(
        validate_simplex(&near_one).expect_err("not one").code(),
        ErrorCode::BadSimplex
    );
}

/// The `0 * log 0 = 0` convention (§7.3): a zero probability contributes an
/// exact zero and never invokes `log 0`.
#[test]
fn zero_probability_contributes_exact_zero() {
    let term = term_enclosure(&Rat::zero(), precision(64)).expect("zero is allowed");
    assert!(term.width().is_zero());
    assert!(term.lower().value().is_zero());
}

#[test]
fn entropy_of_uniform_power_of_two_is_exact() {
    for exponent in 1..=6u32 {
        let size = 1usize << exponent;
        let probability = Rat::from_signeds(1, size as i64);
        let distribution = vec![probability; size];
        let enclosure = entropy_enclosure(&distribution, precision(64)).expect("valid");
        assert!(
            enclosure.width().is_zero(),
            "uniform on 2^{exponent} should be exact"
        );
        assert_eq!(
            *enclosure.lower().value(),
            Rat::from_integer(i64::from(exponent))
        );
    }
}

#[test]
fn entropy_of_a_point_mass_is_zero() {
    let distribution = [Rat::one(), Rat::zero(), Rat::zero()];
    let enclosure = entropy_enclosure(&distribution, precision(64)).expect("valid");
    assert!(enclosure.width().is_zero());
    assert!(enclosure.lower().value().is_zero());
}

#[test]
fn entropy_of_the_uniform_triple_matches_the_reference() {
    let third = Rat::from_signeds(1, 3);
    let distribution = [third.clone(), third.clone(), third];
    let enclosure = entropy_enclosure(&distribution, precision(128)).expect("valid");
    let reference = decimal(
        "1.5849625007211561814537389439478165087598144076924810604557526545410982277943585625222804749180882420909806624750591673437175524410609248221420839506216982994936575922385852344415825363027476853069780516875995",
    );
    assert!(
        enclosure.contains(&reference),
        "H(1/3,1/3,1/3) = {enclosure}"
    );
}

/// §7.6: a zero weight yields exactly zero without evaluating a division.
#[test]
fn zero_weight_conditional_mixture_short_circuits() {
    let numerator = [Rat::zero(), Rat::zero()];
    let result = weighted_conditional_entropy(&Rat::zero(), &numerator, precision(64))
        .expect("zero weight is defined");
    assert!(result.width().is_zero());
    assert!(result.lower().value().is_zero());
}

#[test]
fn nonzero_weight_conditional_mixture_normalizes() {
    let numerator = [Rat::from_signeds(1, 4), Rat::from_signeds(1, 4)];
    let weight = Rat::from_signeds(1, 2);
    let result = weighted_conditional_entropy(&weight, &numerator, precision(64)).expect("valid");
    // The normalized distribution is uniform on two points, so H = 1 and the
    // weighted value is exactly 1/2.
    assert!(result.width().is_zero());
    assert_eq!(*result.lower().value(), Rat::from_signeds(1, 2));
}

#[test]
fn nonzero_weight_with_empty_numerator_rejects() {
    let numerator = [Rat::zero(), Rat::zero()];
    assert_eq!(
        weighted_conditional_entropy(&Rat::one(), &numerator, precision(64))
            .expect_err("no mass")
            .code(),
        ErrorCode::BadSimplex
    );
}

#[test]
fn max_entropy_upper_adds_two_epsilon_and_rejects_negative_epsilon() {
    let witness = [Rat::from_signeds(1, 2), Rat::from_signeds(1, 2)];
    let epsilon = Rat::from_signeds(1, 8);
    let bound = max_entropy_upper(&witness, &epsilon, precision(64)).expect("valid");
    // H(y) = 1 exactly, so the bound is 1 + 2*(1/8) = 5/4.
    assert_eq!(*bound.value(), Rat::from_signeds(5, 4));

    assert_eq!(
        max_entropy_upper(&witness, &Rat::from_signeds(-1, 8), precision(64))
            .expect_err("negative epsilon")
            .code(),
        ErrorCode::NegativeEpsilon
    );
}

/// `docs/specs/0002_spec.md` Appendix A, asserted directly so that a
/// transcription slip fails at `just test` and not only at `just test-diff`.
///
/// Each row is `(z numerator, z denominator, precision, seriesLength)`, and the
/// mantissa each `z` derives from through `z = (m-1)/(m+1)` is named in the
/// comment. The file `tests/vectors/series-length.json` carries the same table
/// as committed data for the cross-implementation stage.
const APPENDIX_A_SERIES_LENGTHS: &[(&str, &str, u32, u32)] = &[
    ("0", "1", 256, 0),                   // m = 1
    ("1", "18446744073709551616", 32, 0), // m = (2^64+1)/(2^64-1)
    ("1", "18446744073709551616", 256, 2),
    ("1", "18446744073709551616", 4096, 32),
    ("1", "9", 256, 40),   // m = 5/4
    ("13", "77", 256, 49), // m = 45/32
    ("1", "5", 256, 54),   // m = 3/2
    ("3", "11", 256, 67),  // m = 7/4
    ("1", "3", 32, 10),    // m = 2, the `ln 2` series
    ("1", "3", 256, 79),
    ("1", "3", 4096, 1290),
];

fn appendix_a_z(numerator: &str, denominator: &str) -> Rat {
    Rat::decode_canonical(numerator, denominator).expect("canonical rational")
}

#[test]
fn series_length_reproduces_appendix_a() {
    for &(numerator, denominator, bits, expected) in APPENDIX_A_SERIES_LENGTHS {
        let z = appendix_a_z(numerator, denominator);
        let selected = series_length(&z, precision(bits)).expect("series length");
        assert_eq!(
            selected, expected,
            "seriesLength({numerator}/{denominator}, {bits}) = {selected}, expected {expected}"
        );
    }
}

#[test]
fn series_length_meets_the_threshold_it_selects() {
    // The Lean specialization theorem `seriesLength_tail_le`, checked here on the
    // same vectors: the selected length meets `2^-(precision+3)` and one term
    // fewer does not, which is what makes it the *least* conforming length.
    for &(numerator, denominator, bits, expected) in APPENDIX_A_SERIES_LENGTHS {
        let z = appendix_a_z(numerator, denominator);
        if z.is_zero() {
            continue;
        }
        let target = precision(bits).series_target().expect("target");
        let one_minus = &Rat::one() - &(&z * &z);
        let tail = |n: u32| {
            let power = z.pow(i64::from(2 * n + 1)).expect("pow");
            power
                .checked_div(&(&Rat::from_integer(i64::from(2 * n + 1)) * &one_minus))
                .expect("tail")
        };
        assert!(
            tail(expected) <= target,
            "seriesLength({numerator}/{denominator}, {bits}) misses its own threshold"
        );
        if expected > 0 {
            assert!(
                tail(expected - 1) > target,
                "seriesLength({numerator}/{denominator}, {bits}) is not the least conforming length"
            );
        }
    }
}

#[test]
fn series_length_matches_fused_loop() {
    // `artanh_enclosure` fuses selection into accumulation so terms are not
    // computed twice; `0002_spec.md` §3.2 makes the fused count an optimization
    // and `series_length` the definition, so the two must agree.
    for &(numerator, denominator, bits, _) in APPENDIX_A_SERIES_LENGTHS {
        let z = appendix_a_z(numerator, denominator);
        let target = precision(bits).series_target().expect("target");
        let fused = artanh_enclosure(&z, &target).expect("series").terms;
        let defined = series_length(&z, precision(bits)).expect("series length");
        assert_eq!(
            fused, defined,
            "fused loop retained {fused} terms where the rule selects {defined}"
        );
    }
}

#[test]
fn a_tiny_nonzero_z_can_retain_no_terms() {
    // The `0002_spec.md` §3.2 fused-loop trap: the mantissa is not 1, so no
    // short circuit fires, yet the tail already meets the threshold before any
    // term is retained. A loop that accumulates before it tests returns 1 here.
    let z = appendix_a_z("1", "18446744073709551616");
    assert!(!z.is_zero());
    let target = precision(32).series_target().expect("target");
    let enclosure = artanh_enclosure(&z, &target).expect("series");
    assert_eq!(enclosure.terms, 0);
    assert_eq!(series_length(&z, precision(32)).expect("length"), 0);
}

#[test]
fn series_length_is_monotone_in_both_arguments() {
    // `0002_spec.md` §2.1: the least conforming length is nondecreasing in `z`
    // and in the precision. §2.3's cap derivation rests on both.
    let grid = [
        Rat::from_signeds(1, 1000),
        Rat::from_signeds(1, 9),
        Rat::from_signeds(1, 5),
        Rat::from_signeds(3, 11),
        Rat::from_signeds(1, 3),
    ];
    for bits in [32u32, 64, 128, 256] {
        let mut previous = 0;
        for z in &grid {
            let selected = series_length(z, precision(bits)).expect("length");
            assert!(
                selected >= previous,
                "length fell from {previous} to {selected} as z grew at {bits} bits"
            );
            previous = selected;
        }
    }
    for z in &grid {
        let mut previous = 0;
        for bits in [32u32, 64, 128, 256, 512, 1024, 4096] {
            let selected = series_length(z, precision(bits)).expect("length");
            assert!(
                selected >= previous,
                "length fell from {previous} to {selected} as precision grew"
            );
            previous = selected;
        }
    }
}

#[test]
fn the_selection_cap_is_far_above_what_the_range_demands() {
    // `0002_spec.md` §2.3: the largest length the supported range can demand is
    // 1,290, at `z = 1/3` and `precision = 4096`.
    let worst =
        series_length(&Rat::from_signeds(1, 3), precision(MAX_PRECISION_BITS)).expect("length");
    assert_eq!(worst, 1_290);
    assert!(worst * 6 < SERIES_LENGTH_CAP);
}

#[test]
fn a_target_below_the_cap_reports_a_resource_limit() {
    // Reaching the cap is a failure, not a result: never a length that misses
    // the threshold, and never a widened threshold. `2^-30000` is out of reach
    // at `z = 1/3`, which needs about 9,464 terms against a cap of 8,192. No
    // precision in `32..=4096` can ask for this, which is the point of the cap.
    let target = Rat::from_integer(2).pow(-30_000).expect("pow");
    let error =
        series_length_for_target(&Rat::from_signeds(1, 3), &target).expect_err("cannot converge");
    assert_eq!(error.code(), ErrorCode::ResourceLimit);
}

/// Pairwise accumulation must give the *same rational*, not a close one.
///
/// `entropy_enclosure` sums its terms by halving rather than left to right,
/// because the directed endpoints carry pairwise-coprime denominators and a
/// sequential accumulator's denominator grows by a fresh factor on every add.
/// Addition in `ℚ` is associative, so the value cannot move — and that is worth
/// a test rather than a comment, because it is the entire licence for the
/// change. A tolerance would defeat the purpose; equality is exact.
#[test]
fn pairwise_entropy_equals_sequential_accumulation() {
    let precision = Precision::new(64).expect("precision");
    let constants = mm_rat::log2::Log2Constants::new(precision).expect("constants");
    for width in [1usize, 2, 3, 5, 8, 17, 33, 64] {
        let distribution: Vec<Rat> = (1..=width)
            .map(|k| Rat::from_signeds(k as i64, (width * (width + 1) / 2) as i64))
            .collect();
        let sum: Rat = mm_rat::rational::sum(distribution.iter());
        assert_eq!(sum, Rat::one(), "width {width} must be a distribution");

        let mut sequential = mm_rat::bounds::Interval::exact(Rat::zero());
        for p in &distribution {
            sequential =
                sequential.add(&mm_rat::entropy::term_enclosure_with(p, &constants).expect("term"));
        }
        let halved = mm_rat::entropy::entropy_enclosure(&distribution, precision).expect("entropy");
        assert_eq!(
            halved.lower().value(),
            sequential.lower().value(),
            "width {width}: the lower endpoint moved under rebracketing"
        );
        assert_eq!(
            halved.upper().value(),
            sequential.upper().value(),
            "width {width}: the upper endpoint moved under rebracketing"
        );
    }
}

/// The fast `scale` must agree with the general product on both signs.
///
/// `scale` no longer routes through `Interval::mul`, so the equivalence that
/// justified the shortcut is pinned here rather than argued in a comment. Zero
/// and both signs of the factor are covered, and so are intervals that straddle
/// zero, which is the case the sign test could plausibly get backwards.
#[test]
fn scaling_agrees_with_general_multiplication() {
    let cases = [(-7i64, 3i64), (-1, 2), (0, 5), (2, 9), (-4, 1)];
    let factors = [
        Rat::from_signeds(-5, 3),
        Rat::from_signeds(-1, 1),
        Rat::zero(),
        Rat::from_signeds(1, 4),
        Rat::from_signeds(11, 2),
    ];
    for (lo, hi) in cases {
        let interval = mm_rat::bounds::Interval::new(
            mm_rat::bounds::LowerBound::assert(Rat::from_signeds(lo, 6)),
            mm_rat::bounds::UpperBound::assert(Rat::from_signeds(hi, 6)),
        )
        .expect("lo <= hi");
        for factor in &factors {
            let fast = interval.scale(factor);
            let general = interval.mul(&mm_rat::bounds::Interval::exact(factor.clone()));
            assert_eq!(
                fast.lower().value(),
                general.lower().value(),
                "lower endpoint differs for [{lo}/6, {hi}/6] * {factor}"
            );
            assert_eq!(
                fast.upper().value(),
                general.upper().value(),
                "upper endpoint differs for [{lo}/6, {hi}/6] * {factor}"
            );
        }
    }
}

/// The rounding arm must land on the grid, and must still enclose.
///
/// Every other test in this file asserts an *enclosure*, which holds in both
/// builds and therefore cannot tell them apart. `docs/adr/0011` claims two
/// things about the enabled arm specifically: that each endpoint lands on the
/// `2^-(precision+32)` grid, and that the enclosure only ever widens. Both are
/// asserted here, and the assertions are `cfg`-gated so the disabled arm pins
/// the complementary claim --- that it is a true no-op.
#[test]
fn outward_rounding_lands_on_the_grid_and_only_widens() {
    use mm_rat::rational::Rat;
    let precision = Precision::new(64).expect("precision");
    // Deliberately awkward arguments: none is a power of two, so none takes the
    // exact-integer early return, and the denominators are coprime to each
    // other so the enclosures cannot share a grid by accident.
    for (numerator, denominator) in [(3i64, 7i64), (5, 11), (1, 3), (97, 101), (2, 5)] {
        let x = Rat::from_signeds(numerator, denominator);
        let enclosure = mm_rat::log2::log2_enclosure(&x, precision).expect("enclosure");
        let lo = enclosure.lower().value();
        let hi = enclosure.upper().value();
        assert!(lo <= hi, "{numerator}/{denominator}: endpoints crossed");

        let grid = precision.bits() + 32;
        let on_grid = |value: &Rat| {
            value.floor_dyadic(grid).expect("floor") == *value
                && value.ceil_dyadic(grid).expect("ceil") == *value
        };
        // Outward dyadic rounding is the registered arithmetic (ADR 0011,
        // `0011_spec.md`): every produced enclosure endpoint sits on the
        // shared `2^-(precision+32)` grid, unconditionally.
        assert!(
            on_grid(lo) && on_grid(hi),
            "{numerator}/{denominator}: an endpoint is off the 2^-{grid} grid"
        );
    }
}
