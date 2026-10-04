//! Certificate-specific Lean module generation (spec §3.5).
//!
//! The generator is **untrusted for mathematical soundness**: even if it emitted
//! different data, the closed Lean checker would still have to validate that data
//! for the theorem's stated claim. What the generator must get right is
//! provenance, and §3.5 pins that down with a round trip: the emitted typed
//! literals are re-encoded and required to be byte-for-byte equal to the
//! published canonical bytes before Lean is invoked.
//!
//! A reduced instance or an unchecked opaque pre-parsed value is forbidden: the
//! generated root module reconstructs the complete semantic certificate.

use mm_core::codes::ErrorCode;
use mm_core::dims::TensorMode;
use mm_core::error::{CoreError, CoreResult};
use mm_schema::AnyDecomposition;
use mm_tensor::ring::{ExactRing, RingTag};

/// The maximum number of rational values in one generated literal shard (§3.5).
pub const MAX_SHARD_VALUES: usize = 50_000;

/// A certification profile (§3.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile {
    /// Kernel-certified: no native-evaluation axiom.
    Ck,
    /// Native-certified: one dedicated native-evaluation axiom.
    Cn,
}

impl Profile {
    /// Parse a profile name.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadConfig`] for an unknown profile.
    pub fn parse(text: &str) -> CoreResult<Self> {
        match text {
            "ck" | "CK" => Ok(Self::Ck),
            "cn" | "CN" => Ok(Self::Cn),
            other => Err(CoreError::new(
                ErrorCode::BadConfig,
                "profile must be \"ck\" or \"cn\"; \"xc\" is never a publication class",
            )
            .equation("§3.4")
            .value(other)),
        }
    }

    /// The canonical name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ck => "CK",
            Self::Cn => "CN",
        }
    }

    /// The human-readable description used in reports (§9.1).
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::Ck => "CK (kernel-certified)",
            Self::Cn => "CN (native-certified)",
        }
    }

    /// The Lean tactic that discharges the closed evaluation.
    #[must_use]
    pub const fn tactic(self) -> &'static str {
        match self {
            Self::Ck => "decide",
            Self::Cn => "native_decide",
        }
    }

    /// The axioms this profile permits for a Track B theorem (§3.4).
    ///
    /// A Track B CK theorem may list only Lean's standard mathematical axioms.
    /// CN permits those plus exactly one certificate-specific native-evaluation
    /// axiom.
    #[must_use]
    pub const fn standard_axioms() -> [&'static str; 3] {
        ["propext", "Classical.choice", "Quot.sound"]
    }
}

/// A generated Lean module together with everything the report needs.
#[derive(Clone, Debug)]
pub struct GeneratedModule {
    /// The fully qualified module name, e.g. `MatrixMath.Generated.Cert_ab12`.
    pub module_name: String,
    /// The module source text.
    pub source: String,
    /// The name of the closed evaluation theorem.
    pub cert_theorem: String,
    /// The name of the published result theorem.
    pub result_theorem: String,
    /// The exact mathematical claim, in human-readable form.
    pub claim: String,
    /// The number of coefficient literals emitted.
    pub literal_count: usize,
    /// The number of shards the literals were split across (§3.5).
    pub shard_count: usize,
}

/// The Lean type and instance imports a ring tag needs.
fn ring_type(decomposition: &AnyDecomposition) -> CoreResult<(String, &'static str)> {
    match decomposition {
        AnyDecomposition::Z(_) => Ok((String::from("Int"), "")),
        AnyDecomposition::Q(_) => Ok((String::from("Rat"), "import Mathlib.Data.Rat.Defs\n")),
        AnyDecomposition::Fp(inner) => Ok((
            format!("(ZMod {})", inner.ring().modulus()),
            "import Mathlib.Data.ZMod.Basic\n",
        )),
        AnyDecomposition::Qi(_) => Ok((
            String::from("MatrixMath.Spec.GaussianRat"),
            "import MatrixMath.Spec.Gaussian\n",
        )),
    }
}

/// Render one coefficient as a Lean literal of the chosen type.
fn lean_literal<R: ExactRing>(ring: &R, value: &R::Elem, tag: RingTag) -> String {
    let text = ring.encode(value);
    match tag {
        // `Z` coefficients are already signed decimal integers.
        RingTag::Z => {
            if text.starts_with('-') {
                format!("({text})")
            } else {
                text
            }
        }
        // `Fp` coefficients are already reduced into `[0,p)`.
        RingTag::Fp => text,
        // `Q` and `Qi` need structured literals, produced by the callers below.
        RingTag::Q | RingTag::Qi => text,
    }
}

fn render_factor<R: ExactRing>(
    ring: &R,
    factor: &[R::Elem],
    tag: RingTag,
    render: &dyn Fn(&R, &R::Elem) -> String,
) -> String {
    let _ = tag;
    let mut out = String::from("[");
    for (index, value) in factor.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&render(ring, value));
    }
    out.push(']');
    out
}

fn render_terms<R: ExactRing>(
    ring: &R,
    terms: &[mm_tensor::Term<R::Elem>],
    tag: RingTag,
    render: &dyn Fn(&R, &R::Elem) -> String,
) -> (Vec<String>, usize) {
    let mut rows = Vec::with_capacity(terms.len());
    let mut count = 0usize;
    for term in terms {
        let mut row = String::from("  ⟨");
        for (index, mode) in TensorMode::ALL.into_iter().enumerate() {
            if index > 0 {
                row.push_str(", ");
            }
            let factor = term.factor(mode);
            count += factor.len();
            row.push_str(&render_factor(ring, factor, tag, render));
        }
        row.push('⟩');
        rows.push(row);
    }
    (rows, count)
}

/// Whether a ring's coefficients reduce in the Lean kernel, and so whether
/// profile CK is reachable for a certificate over it (§3.4).
///
/// `Int` and `ZMod p` reduce. Lean core's `Rat` does not: its arithmetic is
/// opaque to the kernel, so `decide` gets stuck on the first coefficient
/// product. That is a property of the `Rat` implementation, not of this
/// checker, and it makes `Q` and `Qi` certificates CN-only today.
///
/// The route to CK for those rings is to verify a denominator-cleared **integer**
/// identity and prove, in `ℚ`, that it implies the rational reconstruction; see
/// `docs/adr/0002-trust-and-certification-profiles.md`. Kernel evaluation is the
/// blocked step, not reasoning about `ℚ`.
#[must_use]
pub fn kernel_reducible(decomposition: &AnyDecomposition) -> bool {
    matches!(
        decomposition,
        AnyDecomposition::Z(_) | AnyDecomposition::Fp(_)
    )
}

/// Generate the certificate-specific Lean module for a decomposition (§3.5).
///
/// # Errors
///
/// Returns [`ErrorCode::UnsupportedInstance`] when profile CK is requested for a
/// ring whose coefficients do not reduce in the kernel, and propagates ring
/// rendering failures.
pub fn generate(
    decomposition: &AnyDecomposition,
    digest_hex: &str,
    profile: Profile,
) -> CoreResult<GeneratedModule> {
    if profile == Profile::Ck && !kernel_reducible(decomposition) {
        return Err(CoreError::new(
            ErrorCode::UnsupportedInstance,
            "profile CK is not reachable for this ring: Lean core's Rat arithmetic \
             is opaque to the kernel, so the closed evaluation cannot reduce. \
             Use --profile cn, which §3.4 permits and §9.2 makes the default.",
        )
        .equation("§3.4")
        .value(format!("ring {}", ring_name(decomposition))));
    }
    let (type_name, extra_import) = ring_type(decomposition)?;
    let short = digest_hex.get(..16).unwrap_or(digest_hex);
    let module_name = format!("MatrixMath.Generated.Cert_{short}");
    let cert_theorem = format!("cert_{digest_hex}");
    let result_theorem = format!("result_{digest_hex}");
    let instance = decomposition.instance();
    let term_count = decomposition.term_count();

    let (rows, literal_count) = match decomposition {
        AnyDecomposition::Z(inner) => {
            render_terms(inner.ring(), inner.terms(), RingTag::Z, &|ring, value| {
                lean_literal(ring, value, RingTag::Z)
            })
        }
        AnyDecomposition::Fp(inner) => {
            render_terms(inner.ring(), inner.terms(), RingTag::Fp, &|ring, value| {
                lean_literal(ring, value, RingTag::Fp)
            })
        }
        AnyDecomposition::Q(inner) => {
            render_terms(inner.ring(), inner.terms(), RingTag::Q, &|_ring, value| {
                format!(
                    "(({} : Rat) / ({} : Rat))",
                    value.numerator_text(),
                    value.denominator_text()
                )
            })
        }
        AnyDecomposition::Qi(inner) => {
            render_terms(inner.ring(), inner.terms(), RingTag::Qi, &|_ring, value| {
                format!(
                    "⟨({} : Rat) / ({} : Rat), ({} : Rat) / ({} : Rat)⟩",
                    value.re.numerator_text(),
                    value.re.denominator_text(),
                    value.im.numerator_text(),
                    value.im.denominator_text()
                )
            })
        }
    };

    let shard_count = rows
        .len()
        .div_ceil(shard_rows(literal_count, rows.len()).max(1));
    let claim = format!(
        "rank_{{{}}}(T[{},{},{}]) <= {}",
        ring_name(decomposition),
        instance.n(),
        instance.m(),
        instance.p(),
        term_count
    );

    let mut source = String::new();
    source.push_str(&format!(
        "/-\n\
         Generated certificate module. Do not edit.\n\n\
         canonical sha256 : {digest_hex}\n\
         claim            : {claim}\n\
         profile          : {}\n\
         spec version     : {}\n\n\
         This module is hashed publication evidence, not a trusted assumption\n\
         (spec §3.3). Its declarations are checked according to §3.4.\n\
         -/\n",
        profile.as_str(),
        mm_core::SPEC_VERSION
    ));
    source.push_str("import MatrixMath.Certificate.Sound\n");
    source.push_str(extra_import);
    source.push_str("\nnamespace MatrixMath.Generated\n\nopen MatrixMath.Certificate\n\n");

    // Emit the complete decoded semantic certificate as typed literals, sharded
    // so that no single definition exceeds the §3.5 literal budget.
    let per_shard = shard_rows(literal_count, rows.len()).max(1);
    let mut shard_names = Vec::new();
    for (index, chunk) in rows.chunks(per_shard).enumerate() {
        let name = format!("shard{index}");
        shard_names.push(name.clone());
        source.push_str(&format!(
            "/-- Literal shard {index} of the decoded certificate (§3.5). -/\n\
             def {name} : List (ArrayTerm {type_name}) := [\n{}\n]\n\n",
            chunk.join(",\n")
        ));
    }

    source.push_str(&format!(
        "/-- The complete decoded semantic certificate. No node or block is\n\
         omitted (§3.5). -/\n\
         def certificate : Decomposition {type_name} where\n\
         \x20 n := {}\n\
         \x20 m := {}\n\
         \x20 p := {}\n\
         \x20 terms := {}\n\n",
        instance.n(),
        instance.m(),
        instance.p(),
        if shard_names.len() == 1 {
            shard_names.join("")
        } else {
            shard_names.join(" ++ ")
        }
    ));

    source.push_str("set_option maxRecDepth 8000000 in\n");
    source.push_str("set_option maxHeartbeats 4000000 in\n");
    source.push_str(&format!(
        "/-- The closed checker evaluation over the complete certificate. -/\n\
         theorem {cert_theorem} :\n\
         \x20   validate certificate = true ∧ certificate.termCount = {term_count} := by\n\
         \x20 refine ⟨by {}, by rfl⟩\n\n",
        profile.tactic()
    ));

    source.push_str(&format!(
        "/-- **{claim}**\n\n\
         Follows from the general soundness theorem applied to the closed\n\
         evaluation above; the term count is a bound, never a minimality claim\n\
         (§10.4). -/\n\
         theorem {result_theorem} :\n\
         \x20   TensorRankLE {type_name} {} {} {} {term_count} := by\n\
         \x20 have h := validate_rank_le {cert_theorem}.1\n\
         \x20 rwa [{cert_theorem}.2] at h\n\n",
        instance.n(),
        instance.m(),
        instance.p()
    ));

    source.push_str(&format!(
        "#print axioms {cert_theorem}\n#print axioms {result_theorem}\n\nend MatrixMath.Generated\n"
    ));

    Ok(GeneratedModule {
        module_name,
        source,
        cert_theorem,
        result_theorem,
        claim,
        literal_count,
        shard_count: shard_count.max(1),
    })
}

fn shard_rows(literal_count: usize, row_count: usize) -> usize {
    if row_count == 0 || literal_count == 0 {
        return 1;
    }
    let per_row = literal_count.div_ceil(row_count).max(1);
    (MAX_SHARD_VALUES / per_row).max(1)
}

fn ring_name(decomposition: &AnyDecomposition) -> String {
    match decomposition {
        AnyDecomposition::Z(_) => String::from("Z"),
        AnyDecomposition::Q(_) => String::from("Q"),
        AnyDecomposition::Fp(inner) => format!("F{}", inner.ring().modulus()),
        AnyDecomposition::Qi(_) => String::from("Q(i)"),
    }
}
