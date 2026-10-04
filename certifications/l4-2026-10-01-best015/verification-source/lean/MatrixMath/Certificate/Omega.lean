import MatrixMath.Axioms
import MatrixMath.Numeric.EntropyBounds

/-!
# Track A directed soundness

Normative source: `docs/specs/0001_spec.md` §7.2, A.10 (A21), §3.2.

The Track A checker evaluates every quantity as a **directed** rational bound and
then checks

```text
lower(E_total) + lower(M_total) * Ω >= 2^(ℓ*-1) * upper(log2(q+2)).
```

`E_total`, `M_total`, and `log2(q+2)` are real and generally irrational, so the
step that actually matters is: *does passing the rational check imply the real
inequality?* That is `directed_implies_real` below, and it is proved.

§7.2 requires `Ω >= 0` to be validated before `lower(M_total)` is multiplied by
it. The proof shows why: the multiplication step is exactly where a negative `Ω`
would reverse the inequality, so `Ω >= 0` appears as a hypothesis rather than as
a comment.

## Where the rest of the chain lives

A21 feasibility is a statement about the **cited** problem of S1 (§A.10).
`MatrixMath.Spec.Instance` writes that problem down and
`MatrixMath.Certificate.OmegaCheck` decides a sufficient condition for accepted
data to be a feasible point of it, so the link from "the directed check passed"
to "this data is feasible for the cited problem" is a theorem, not an assumption.
This module supplies the numeric half of that link.
-/

namespace MatrixMath.Certificate

open MatrixMath.Numeric

/-- The real A21 inequality (A21). -/
def A21Holds (eTotal mTotal omega requirement : ℝ) : Prop :=
  requirement ≤ eTotal + mTotal * omega

/-- **The directed check implies the real inequality** (§7.2, A21).

Given
* a rational lower bound for `E_total`,
* a rational lower bound for `M_total`,
* a rational upper bound for the requirement `2^(ℓ*-1) log2(q+2)`,
* a **nonnegative** `Ω`, and
* the rational inequality the checker actually evaluates,

the real inequality follows.

`Ω >= 0` is not decoration: it is what lets `mLow ≤ mTotal` be multiplied through
without reversing. §7.2 says a future signed multiplier must use general interval
multiplication instead, and this proof is why. -/
theorem directed_implies_real
    {eTotal mTotal requirement : ℝ} {eLow mLow reqHigh omega : ℚ}
    (hE : (eLow : ℝ) ≤ eTotal)
    (hM : (mLow : ℝ) ≤ mTotal)
    (hReq : requirement ≤ (reqHigh : ℝ))
    (hOmega : 0 ≤ omega)
    (hCheck : reqHigh ≤ eLow + mLow * omega) :
    A21Holds eTotal mTotal (omega : ℝ) requirement := by
  unfold A21Holds
  have hOmega' : (0 : ℝ) ≤ (omega : ℝ) := by exact_mod_cast hOmega
  have hCheck' : (reqHigh : ℝ) ≤ (eLow : ℝ) + (mLow : ℝ) * (omega : ℝ) := by
    exact_mod_cast hCheck
  -- The only place the sign of omega matters.
  have hMul : (mLow : ℝ) * (omega : ℝ) ≤ mTotal * (omega : ℝ) :=
    mul_le_mul_of_nonneg_right hM hOmega'
  linarith

/-- A negative multiplier really does break the step, which is why §7.2 demands
the `Ω >= 0` validation rather than trusting the certificate.

Concretely: with `mLow = 0 ≤ mTotal = 1` and `omega = -1`, the rational check
passes and the real inequality fails. -/
theorem directed_needs_nonneg_omega :
    ∃ (eTotal mTotal requirement : ℝ) (eLow mLow reqHigh omega : ℚ),
      (eLow : ℝ) ≤ eTotal ∧ (mLow : ℝ) ≤ mTotal ∧ requirement ≤ (reqHigh : ℝ) ∧
        reqHigh ≤ eLow + mLow * omega ∧
        ¬ A21Holds eTotal mTotal (omega : ℝ) requirement := by
  refine ⟨0, 1, 0, 0, 0, 0, -1, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · unfold A21Holds
    norm_num

end MatrixMath.Certificate
