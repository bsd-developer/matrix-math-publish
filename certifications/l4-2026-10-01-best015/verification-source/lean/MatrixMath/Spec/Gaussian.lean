import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Gaussian rationals

Normative source: `docs/specs/0001_spec.md` §6.6 (`Qi` ring tag) and Appendix B.7.

Version 1's complex scope is exactly `ℚ(i)`, represented by rational pairs with

```text
(a+bi)+(c+di) = (a+c)+(b+d)i
(a+bi)(c+di) = (ac-bd)+(ad+bc)i
```

This embeds into `ℂ`, so a valid `Qi` decomposition is a complex decomposition
(B.7). The checker makes no claim about decompositions requiring other algebraic
or transcendental coefficients; those are rejected as unsupported (§0.2).

Mathlib's `GaussianInt` is `ℤ[i]`, not `ℚ(i)`, and `Complex` is neither
computable nor decidably equal, so neither can carry an executable certificate
check. This type is defined here so the generated certificate modules have a
`CommRing` with `DecidableEq` that reduces in the kernel (profile CK).
-/

namespace MatrixMath.Spec

/-- A Gaussian rational `re + im * i` (Appendix B.7). -/
structure GaussianRat where
  /-- The real component. -/
  re : ℚ
  /-- The imaginary component. -/
  im : ℚ
  deriving DecidableEq, Repr

namespace GaussianRat

@[ext]
theorem ext {a b : GaussianRat} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

instance : Zero GaussianRat := ⟨⟨0, 0⟩⟩
instance : One GaussianRat := ⟨⟨1, 0⟩⟩
instance : Add GaussianRat := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Neg GaussianRat := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance : Sub GaussianRat := ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩
instance : Mul GaussianRat :=
  ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩

@[simp] theorem zero_re : (0 : GaussianRat).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussianRat).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussianRat).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussianRat).im = 0 := rfl
@[simp] theorem add_re (a b : GaussianRat) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : GaussianRat) : (a + b).im = a.im + b.im := rfl
@[simp] theorem neg_re (a : GaussianRat) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : GaussianRat) : (-a).im = -a.im := rfl
@[simp] theorem sub_re (a b : GaussianRat) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : GaussianRat) : (a - b).im = a.im - b.im := rfl
@[simp] theorem mul_re (a b : GaussianRat) :
    (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : GaussianRat) :
    (a * b).im = a.re * b.im + a.im * b.re := rfl

instance instCommRing : CommRing GaussianRat where
  add_assoc _ _ _ := by ext <;> simp <;> ring
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp <;> ring
  neg_add_cancel _ := by ext <;> simp
  sub_eq_add_neg _ _ := by ext <;> simp <;> ring
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The field norm `a^2 + b^2`, which is zero only at zero. -/
def norm (a : GaussianRat) : ℚ := a.re * a.re + a.im * a.im

theorem norm_eq_zero_iff {a : GaussianRat} : a.norm = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hsplit : a.re * a.re = 0 ∧ a.im * a.im = 0 :=
      (add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (mul_self_nonneg _)).mp h
    exact ext (mul_self_eq_zero.mp hsplit.1) (mul_self_eq_zero.mp hsplit.2)
  · rintro rfl
    simp [norm]

end GaussianRat

end MatrixMath.Spec
