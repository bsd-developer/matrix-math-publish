import MatrixMath.Spec.Instance
import MatrixMath.Spec.OmegaExponent

/-!
# Project axioms

Normative source: `docs/specs/0001_spec.md` §3.2, A.10.

This module declares **exactly one** project axiom. §3.2 fixes what a top-level
Track A theorem may depend on:

* `AX1_combination_loss`, the cited theorem of Alman et al. bridging feasibility
  of the Appendix A.10 problem to a bound on `ω`;
* Lean's standard mathematical axioms, as introduced by Mathlib; and
* under profile CN only, one certificate-specific native-evaluation axiom.

It MUST NOT depend on `sorryAx`, an undeclared project axiom, MPFR correctness,
the Rust checker, the optimizer, or the certificate producer. `mm prove` enforces
that mechanically by parsing `#print axioms` output.

Lean kernel soundness is a **metatheoretic assumption**, not a Lean axiom. §3.2
requires it to appear only in the TCB ledger and forbids labelling it in
`#print axioms` output, so it is deliberately absent from this file.

Track B needs no project axiom at all: `MatrixMath.Certificate.validate_rank_le`
depends only on `propext` and `Quot.sound`.
-/

namespace MatrixMath

/-- **AX1.** The cited theorem of Alman et al.: feasibility of the S1
combination-loss problem implies a bound on the matrix multiplication exponent.

This is the one project axiom version 1 permits (§3.2). Both sides of the
implication are now *defined* rather than opaque: the hypothesis is
`MatrixMath.CombinationLossFeasible`, which `MatrixMath.Spec.Instance` defines
as the A.1–A.10 problem, and the conclusion bounds
`MatrixMath.omegaExponent`, which `MatrixMath.Spec.OmegaExponent` defines over
`ℚ` by the infimum characterization (`docs/adr/0013-definitional-omega.md`) —
so the axiom asserts a checkable statement about the exponent itself, not a
relation to a black-box constant. The cited theorem holds over every field;
asserting its `ℚ` specialization is the weaker direction. The definition
deliberately omits version 1's `Ω ≥ 0` restriction: §A.10 says that
restriction only narrows the feasible set, and it belongs to the directed
evaluator, not to the cited problem.

Version 1 does not prove this. Formalizing the laser method and combination-loss
analysis from first principles is an explicit non-goal (§1.4). -/
axiom AX1_combination_loss :
    ∀ {q levels : ℕ} {Ω : ℝ}, CombinationLossFeasible q levels Ω → omegaExponent ≤ Ω

end MatrixMath
