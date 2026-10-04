import MatrixMath.Numeric.EntropyBounds
import MatrixMath.Spec.Basic

/-!
# Appendix A.3 entropy and penalty

Normative source: `docs/specs/0001_spec.md` A.3, §7.3, §7.4, §7.6.

```text
H(ρ)        = - Σ_{x ∈ supp ρ} ρ(x) log2 ρ(x)
H_D^max(ρ)  = sup { H(ρ') : ρ' ∈ Δ(D), ρ'_W = ρ_W for W = X,Y,Z }   (A1)
P_D(ρ)      = H_D^max(ρ) - H(ρ)
```

The executable directed bounds live in `MatrixMath.Numeric.EntropyBounds`; this
module states the mathematical objects they bound, and the §7.6 guarded
conditional mixture, whose whole point is that division by zero is never
evaluated.
-/

namespace MatrixMath.Spec

open Finset MatrixMath.Numeric

variable {ι : Type*}

/-- `Δ(D)`: the distributions on a finite domain (A.2). -/
def IsDistribution (s : Finset ι) (p : ι → ℝ) : Prop :=
  (∀ a ∈ s, 0 ≤ p a) ∧ ∑ a ∈ s, p a = 1

/-- Two distributions agree in a coordinate marginal when every fibre carries the
same mass. `key` is the coordinate map, for example `fun shape => shape.x`. -/
def SameMarginal {κ : Type*} [DecidableEq κ] (s : Finset ι) (key : ι → κ)
    (p q : ι → ℝ) : Prop :=
  ∀ v : κ, ∑ a ∈ s.filter (fun a => key a = v), p a
         = ∑ a ∈ s.filter (fun a => key a = v), q a

/-- The feasible set of A1: distributions on `D` matching all three marginals of
`ρ`. -/
def MarginalFeasible {κ : Type*} [DecidableEq κ] (s : Finset ι)
    (kx ky kz : ι → κ) (rho p : ι → ℝ) : Prop :=
  IsDistribution s p ∧ SameMarginal s kx rho p ∧ SameMarginal s ky rho p
    ∧ SameMarginal s kz rho p

/-- `H_D^max(ρ)` as the supremum of A1, and `P_D(ρ) = H_D^max(ρ) - H(ρ)`.

A `MaxEntropyBound` is a witnessed **upper** bound for that supremum: `b` bounds
the entropy of every feasible `ρ'`. §7.4's block produces exactly this, and
`MatrixMath.Numeric.entropy_le_of_close` is what discharges the field. -/
structure MaxEntropyBound {κ : Type*} [DecidableEq κ] (s : Finset ι)
    (kx ky kz : ι → κ) (rho : ι → ℝ) where
  /-- The claimed bound. -/
  bound : ℝ
  /-- Every feasible distribution has entropy at most `bound`. -/
  le : ∀ p, MarginalFeasible s kx ky kz rho p → entropy s p ≤ bound

/-- The penalty `P_D(ρ)` bounded above using a maximum-entropy bound (A1).

`P_D(ρ) = H_D^max(ρ) - H(ρ)`, so an upper bound for `H_D^max` and a lower bound
for `H(ρ)` give an upper bound for the penalty — which is the direction §7.2
needs, since `E` subtracts the penalty. -/
def penaltyUpper {κ : Type*} [DecidableEq κ] {s : Finset ι} {kx ky kz : ι → κ}
    {rho : ι → ℝ} (b : MaxEntropyBound s kx ky kz rho) (hRhoLower : ℝ) : ℝ :=
  b.bound - hRhoLower

/-- The §7.6 guarded conditional mixture.

Appendix A uses the convention `0 · undefined := 0`. This is a **branch**, not a
limit: at zero weight the value is zero and the normalization is never performed,
so no division by zero is ever evaluated. -/
noncomputable def weightedConditionalEntropy (s : Finset ι) (weight : ℝ)
    (numerator : ι → ℝ) : ℝ :=
  if weight = 0 then 0 else weight * entropy s (fun a => numerator a / weight)

@[simp] theorem weightedConditionalEntropy_zero (s : Finset ι) (numerator : ι → ℝ) :
    weightedConditionalEntropy s 0 numerator = 0 := by
  simp [weightedConditionalEntropy]

theorem weightedConditionalEntropy_of_ne {s : Finset ι} {weight : ℝ}
    (h : weight ≠ 0) (numerator : ι → ℝ) :
    weightedConditionalEntropy s weight numerator
      = weight * entropy s (fun a => numerator a / weight) := by
  simp [weightedConditionalEntropy, h]

/-- The entropy of the empty domain is zero, which is what makes the zero branch
above agree with the limit rather than merely being a convention of convenience. -/
@[simp] theorem entropy_empty (p : ι → ℝ) : entropy (∅ : Finset ι) p = 0 := by
  simp [entropy]

end MatrixMath.Spec
