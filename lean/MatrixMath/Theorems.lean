import Lean
import MatrixMath.Certificate.Sound
import MatrixMath.Certificate.Omega
import MatrixMath.Certificate.OmegaCheck
import MatrixMath.Schema.Decode
import MatrixMath.Schema.Omega
import MatrixMath.Spec.Entropy
import MatrixMath.Numeric.EntropyBounds

/-!
# Public theorem inventory

Normative source: `docs/specs/0001_spec.md` §4.6.

Every public formal claim the project makes is enumerated here by **exact fully
qualified declaration name**. `MatrixMath.AssuranceAudit` resolves each name in
Lean's compiled environment and reports its kind, statement text and digest,
sorted transitive axioms, and required evidence. Source-text searches and
theorem-name strings are explicitly not substitutes (§4.6), which is why this
list carries `Name` values that must actually resolve.

Certificate-specific generated declarations are **not** appended here: `just
prove` emits a result-local `assurance.json` instead (§4.6).
-/

namespace MatrixMath

/-- One audited public claim. -/
structure ClaimEntry where
  /-- Stable claim identifier, e.g. `B-SOUND-1`. -/
  id : String
  /-- Exact fully qualified Lean declaration name. -/
  declName : Lean.Name
  /-- The fixture, mutation, or qualification evidence this claim requires. -/
  evidence : List String
  /-- Project axioms this claim is permitted to depend on (§4.6 "applicable
  allowlist"). Lean's standard mathematical axioms are always permitted and are
  not listed. §3.2 permits exactly one project axiom in this development, so a
  nonempty allowlist here names `AX1_combination_loss` and nothing else. -/
  allowlist : List String := []
  /-- Residual assumptions, which must be empty for a publication-class claim. -/
  residual : List String
  /-- `active`, `superseded`, or `experimental`. -/
  status : String
  deriving Repr

/-- Public formal claims audited at the current milestone (§4.6). -/
def publicTheoremInventory : List ClaimEntry := [
  { id := "B-TENSOR-1"
    declName := `MatrixMath.Spec.targetCoeff_support
    evidence := ["schemas/fixtures/valid", "tests/vectors/naive-2x2x2-z.json"]
    residual := []
    status := "active" },
  { id := "B-TENSOR-2"
    declName := `MatrixMath.Spec.targetCoeff_as_indicators
    evidence := ["crates/mm-tensor/tests/properties.rs::target_support_matches_the_entrywise_definition"]
    residual := []
    status := "active" },
  { id := "B-ALGO-1"
    declName := `MatrixMath.Spec.reconstructs_bilinear
    evidence := ["tests/vectors/strassen-z.json", "tests/vectors/naive-2x3x4-z.json"]
    residual := []
    status := "active" },
  { id := "B-SOUND-1"
    declName := `MatrixMath.Certificate.validate_sound
    evidence := ["schemas/fixtures/invalid/reconstruction_mismatch.json"]
    residual := []
    status := "active" },
  { id := "B-SOUND-2"
    declName := `MatrixMath.Certificate.validate_rank_le
    evidence := ["tests/vectors/alphatensor-f2-4x4x4.json"]
    residual := []
    status := "active" },
  { id := "B-SOUND-3"
    declName := `MatrixMath.Certificate.validate_computes_matmul
    evidence := ["tests/vectors/strassen-z.json"]
    residual := []
    status := "active" },
  { id := "A-LOG-1"
    declName := `MatrixMath.Numeric.log2Lower_le
    evidence := ["crates/mm-rat/tests/numerics.rs::log2_encloses_independent_reference_values"]
    residual := []
    status := "active" },
  { id := "A-LOG-2"
    declName := `MatrixMath.Numeric.le_log2Upper
    evidence := ["crates/mm-rat/tests/numerics.rs::log2_encloses_independent_reference_values"]
    residual := []
    status := "active" },
  { id := "A-LOG-3"
    declName := `MatrixMath.Numeric.logPartial_le
    evidence := ["crates/mm-rat/tests/numerics.rs::ln2_and_its_reciprocal_enclose_reference_values"]
    residual := []
    status := "active" },
  { id := "A-LOG-4"
    declName := `MatrixMath.Numeric.le_logPartial_add_tail
    evidence := ["crates/mm-rat/tests/numerics.rs::log2_encloses_independent_reference_values"]
    residual := []
    status := "active" },
  { id := "A-LOG-5"
    declName := `MatrixMath.Numeric.seriesLength_tail_le
    evidence := ["tests/vectors/series-length.json"]
    residual := []
    status := "active" },
  { id := "A-ENT-1"
    declName := `MatrixMath.Numeric.entropyLower_le
    evidence := ["crates/mm-rat/tests/numerics.rs::entropy_of_uniform_power_of_two_is_exact"]
    residual := []
    status := "active" },
  { id := "A-ENT-2"
    declName := `MatrixMath.Numeric.le_entropyUpper
    evidence := ["crates/mm-rat/tests/numerics.rs::entropy_of_the_uniform_triple_matches_the_reference"]
    residual := []
    status := "active" },
  { id := "A-ENT-3"
    declName := `MatrixMath.Numeric.sum_mul_logb_le
    evidence := ["crates/mm-rat/tests/numerics.rs::entropy_of_a_point_mass_is_zero"]
    residual := []
    status := "active" },
  -- A22 itself. §A.11 forbids a project axiom here, so this row exists to make a
  -- regression visible in the audit rather than only in a proof file.
  { id := "A22"
    declName := `MatrixMath.Numeric.entropy_le_of_close
    evidence := ["crates/mm-rat/tests/numerics.rs::max_entropy_upper_adds_two_epsilon_and_rejects_negative_epsilon"]
    residual := []
    status := "active" },
  { id := "A-BOUND-1"
    declName := `MatrixMath.Numeric.Enclosure.mulGeneral
    evidence := ["crates/mm-rat/tests/numerics.rs::interval_multiplication_is_sign_aware"]
    residual := []
    status := "active" },
  { id := "A-BOUND-2"
    declName := `MatrixMath.Numeric.Enclosure.divPos
    evidence := ["crates/mm-rat/tests/numerics.rs::nonnegative_scaling_rejects_a_signed_multiplier"]
    residual := []
    status := "active" },
  { id := "DOMAIN-1"
    declName := `MatrixMath.Spec.Region.permute_injective
    evidence := ["crates/mm-core/tests/domains.rs::region_permutation_table_is_normative"]
    residual := []
    status := "active" },
  { id := "DOMAIN-2"
    declName := `MatrixMath.Spec.Region.permute_surjective
    evidence := ["crates/mm-core/tests/domains.rs::region_permutation_is_a_bijection_with_exact_inverse"]
    residual := []
    status := "active" },
  { id := "DOMAIN-3"
    declName := `MatrixMath.Spec.NodePath.distinct_paths_same_last
    evidence := ["crates/mm-core/tests/domains.rs::node_paths_distinguish_identical_level_shape_region"]
    residual := []
    status := "active" },
  -- §3.1's authoritative shape: the hypothesis is about bytes, not about
  -- prevalidated data, which is what §17.5 requires when the publication command
  -- accepts bytes.
  { id := "BYTES-SOUND"
    declName := `MatrixMath.Schema.checkBytes_sound
    evidence := ["lean/scripts/DecodeCheck.lean", "tests/vectors/alphatensor-f2-4x4x4.json"]
    residual := []
    status := "active" },
  { id := "BYTES-RANK"
    declName := `MatrixMath.Schema.checkBytes_rank_le
    evidence := ["lean/scripts/DecodeCheck.lean", "tests/vectors/alphatensor-f2-4x4x4.json"]
    residual := []
    status := "active" },
  { id := "A21-DIRECTED"
    declName := `MatrixMath.Certificate.directed_implies_real
    evidence := ["crates/mm-exact/tests/omega_fixtures.rs::the_hand_fixture_evaluates_and_satisfies_a21"]
    residual := []
    status := "active" },
  { id := "A21-SIGN"
    declName := `MatrixMath.Certificate.directed_needs_nonneg_omega
    evidence := ["crates/mm-exact/tests/appendix_a.rs::a_negative_omega_is_rejected_before_multiplication"]
    residual := []
    status := "active" },
  { id := "A22-BLOCK"
    declName := `MatrixMath.Spec.hMaxOf_le_of_block
    evidence := ["crates/mm-exact/tests/omega_fixtures.rs::the_hand_fixture_evaluates_and_satisfies_a21"]
    residual := []
    status := "active" },
  { id := "A21-FEASIBLE"
    declName := `MatrixMath.Certificate.TrackACert.check_sound
    evidence := ["tests/vectors/omega-l2-hand.json"]
    residual :=
      ["Demonstrated at ℓ* = 2 and ℓ* = 3. The checker covers §0.2's whole \
        range; ℓ* = 4 has not been run, and §16 fixes the fallback if it \
        exceeds H64."]
    status := "active" },
  -- The Track A conclusion. Its transitive axioms must be exactly Lean's
  -- standard set plus AX1_combination_loss; anything else is a release failure
  -- (§3.2, §3.4), and the audit is what makes that visible.
  { id := "OMEGA-BYTES"
    declName := `MatrixMath.Schema.checkOmegaBytes_sound
    evidence := ["lean/scripts/DecodeCheck.lean", "tests/vectors/omega-l2-optimized.json"]
    residual :=
      ["Demonstrated at ℓ* = 2 and ℓ* = 3. The decoder accepts §0.2's whole \
        range; ℓ* = 4 has not been run, and §16 fixes the fallback if it \
        exceeds H64."]
    status := "active" },
  { id := "A21-OMEGA"
    declName := `MatrixMath.Schema.omega_le_of_acceptsOmega
    evidence := ["tests/vectors/omega-l2-optimized.json"]
    allowlist := ["MatrixMath.AX1_combination_loss"]
    residual :=
      ["Demonstrated at ℓ* = 2 and ℓ* = 3. The checker covers §0.2's whole \
        range; ℓ* = 4 has not been run, and §16 fixes the fallback if it \
        exceeds H64."]
    status := "experimental" },
  { id := "A21-OMEGA-DIGEST"
    declName := `MatrixMath.Schema.omega_le_of_acceptsOmegaDigest
    evidence := ["tests/vectors/omega-l2-optimized.json"]
    allowlist := ["MatrixMath.AX1_combination_loss"]
    residual :=
      ["Extends A21-OMEGA with the §6.3 artifact identity folded into the \
        same single native evaluation: generated modules bind their byte \
        literal to the published digest inside the theorem. Same residuals \
        as A21-OMEGA."]
    status := "experimental" }]

end MatrixMath
