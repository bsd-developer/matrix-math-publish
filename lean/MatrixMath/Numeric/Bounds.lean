import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity

/-!
# Directed rational bounds

Normative source: `docs/specs/0001_spec.md` §7.1, §7.2, §14.7.

§7.1 requires the authoritative evaluator to make bound **direction** visible and
forbids a single ambiguous `log2` or `entropy` method. In Lean the strongest way
to do that is to make a bound carry its own proof: an `Enclosure x` is a pair of
rationals together with evidence that they bracket the real number `x`. A
propagation rule that gets a direction wrong then simply fails to typecheck.

`Enclosure x` is computable data: `x` appears only in the types of the erased
proof fields, so the bounds themselves are ordinary rationals at runtime.
-/

namespace MatrixMath.Numeric

open Set

/-- A rational lower bound for a real quantity (§7.1). -/
structure LowerBound (x : ℝ) where
  /-- The rational value. -/
  value : ℚ
  /-- Evidence that it really is below `x`. -/
  le : (value : ℝ) ≤ x

/-- A rational upper bound for a real quantity (§7.1). -/
structure UpperBound (x : ℝ) where
  /-- The rational value. -/
  value : ℚ
  /-- Evidence that it really is above `x`. -/
  ge : x ≤ (value : ℝ)

/-- A validated rational enclosure `[lo, hi]` of a real quantity (§7.1). -/
structure Enclosure (x : ℝ) where
  /-- The lower endpoint. -/
  lo : ℚ
  /-- The upper endpoint. -/
  hi : ℚ
  /-- Evidence for the lower endpoint. -/
  lo_le : (lo : ℝ) ≤ x
  /-- Evidence for the upper endpoint. -/
  le_hi : x ≤ (hi : ℝ)

namespace Enclosure

variable {x y : ℝ}

/-- The endpoints are ordered, which §7.1 requires of every interval. -/
theorem lo_le_hi (e : Enclosure x) : e.lo ≤ e.hi := by
  have : (e.lo : ℝ) ≤ (e.hi : ℝ) := le_trans e.lo_le e.le_hi
  exact_mod_cast this

/-- The exact enclosure of a rational value. -/
def exact (q : ℚ) : Enclosure (q : ℝ) :=
  { lo := q, hi := q, lo_le := le_rfl, le_hi := le_rfl }

/-- The width `hi - lo`, which §12.6 reports rather than comparing midpoints. -/
def width (e : Enclosure x) : ℚ := e.hi - e.lo

theorem width_nonneg (e : Enclosure x) : 0 ≤ e.width := by
  have := e.lo_le_hi
  simp [width]
  linarith

/-- Lower bound of a sum is the sum of lower bounds (§7.2). -/
def add (a : Enclosure x) (b : Enclosure y) : Enclosure (x + y) where
  lo := a.lo + b.lo
  hi := a.hi + b.hi
  lo_le := by push_cast; exact add_le_add a.lo_le b.lo_le
  le_hi := by push_cast; exact add_le_add a.le_hi b.le_hi

/-- Lower bound of `x - y` is `lower x - upper y` (§7.2): the direction reverses
on the subtrahend, and stating it this way is what makes that impossible to get
wrong. -/
def sub (a : Enclosure x) (b : Enclosure y) : Enclosure (x - y) where
  lo := a.lo - b.hi
  hi := a.hi - b.lo
  lo_le := by push_cast; exact sub_le_sub a.lo_le b.le_hi
  le_hi := by push_cast; exact sub_le_sub a.le_hi b.lo_le

/-- Negation swaps and negates the endpoints. -/
def neg (a : Enclosure x) : Enclosure (-x) where
  lo := -a.hi
  hi := -a.lo
  lo_le := by push_cast; exact neg_le_neg a.le_hi
  le_hi := by push_cast; exact neg_le_neg a.lo_le

/-- Scaling by a **nonnegative** rational preserves direction (§7.2). -/
def scaleNonneg (a : Enclosure x) {c : ℚ} (hc : 0 ≤ c) : Enclosure ((c : ℝ) * x) where
  lo := c * a.lo
  hi := c * a.hi
  lo_le := by
    push_cast
    exact mul_le_mul_of_nonneg_left a.lo_le (by exact_mod_cast hc)
  le_hi := by
    push_cast
    exact mul_le_mul_of_nonneg_left a.le_hi (by exact_mod_cast hc)

/-- Scaling by a **nonpositive** rational reverses direction (§7.3).

This is the rule the entropy term `-p * log2 p` needs: multiplying a logarithm
enclosure by `-p` swaps which endpoint is which. -/
def scaleNonpos (a : Enclosure x) {c : ℚ} (hc : c ≤ 0) : Enclosure ((c : ℝ) * x) where
  lo := c * a.hi
  hi := c * a.lo
  lo_le := by
    push_cast
    exact mul_le_mul_of_nonpos_left a.le_hi (by exact_mod_cast hc)
  le_hi := by
    push_cast
    exact mul_le_mul_of_nonpos_left a.lo_le (by exact_mod_cast hc)

/-- Shift by an exact rational. -/
def shift (a : Enclosure x) (c : ℚ) : Enclosure ((c : ℝ) + x) where
  lo := c + a.lo
  hi := c + a.hi
  lo_le := by push_cast; linarith [a.lo_le]
  le_hi := by push_cast; linarith [a.le_hi]

/-- Widen an enclosure to any weaker pair of bounds. -/
def widen (a : Enclosure x) {lo hi : ℚ} (hlo : lo ≤ a.lo) (hhi : a.hi ≤ hi) :
    Enclosure x where
  lo := lo
  hi := hi
  lo_le := le_trans (by exact_mod_cast hlo) a.lo_le
  le_hi := le_trans a.le_hi (by exact_mod_cast hhi)

/-- Transport an enclosure along an equality of the enclosed quantity. -/
def cast (a : Enclosure x) (h : x = y) : Enclosure y where
  lo := a.lo
  hi := a.hi
  lo_le := h ▸ a.lo_le
  le_hi := h ▸ a.le_hi

/-- Product of two **nonnegative** enclosures (§7.2 monotonic shortcut).

The nonnegativity hypotheses are exactly the validation §7.2 demands before the
shortcut may be used; a signed factor must go through `mulGeneral`. -/
def mulNonneg (a : Enclosure x) (b : Enclosure y) (hx : 0 ≤ a.lo) (hy : 0 ≤ b.lo) :
    Enclosure (x * y) where
  lo := a.lo * b.lo
  hi := a.hi * b.hi
  lo_le := by
    push_cast
    have hx' : (0 : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast hx
    have hy' : (0 : ℝ) ≤ (b.lo : ℝ) := by exact_mod_cast hy
    exact mul_le_mul a.lo_le b.lo_le hy' (le_trans hx' a.lo_le)
  le_hi := by
    push_cast
    have hx' : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast hx) a.lo_le
    have hy' : (0 : ℝ) ≤ y := le_trans (by exact_mod_cast hy) b.lo_le
    exact mul_le_mul a.le_hi b.le_hi hy' (le_trans hx' a.le_hi)

/-- The four endpoint products bracket the product of two bracketed reals.

Proved by the sign of `y` and then the sign of the relevant `x` endpoint, which
is the whole content of "sign-aware": with `y ≥ 0` the product is monotone in
`x`, and with `y < 0` it is antitone. -/
private theorem mul_mem_endpoints {xl xh x yl yh y : ℝ}
    (hx1 : xl ≤ x) (hx2 : x ≤ xh) (hy1 : yl ≤ y) (hy2 : y ≤ yh) :
    min (min (xl * yl) (xl * yh)) (min (xh * yl) (xh * yh)) ≤ x * y ∧
      x * y ≤ max (max (xl * yl) (xl * yh)) (max (xh * yl) (xh * yh)) := by
  constructor
  · rcases le_total 0 y with hy | hy
    · rcases le_total 0 xl with hxl | hxl
      -- xl*yl ≤ xl*y ≤ x*y
      · exact min_le_of_left_le (min_le_of_left_le
          ((mul_le_mul_of_nonneg_left hy1 hxl).trans (mul_le_mul_of_nonneg_right hx1 hy)))
      -- xl*yh ≤ xl*y ≤ x*y
      · exact min_le_of_left_le (min_le_of_right_le
          ((mul_le_mul_of_nonpos_left hy2 hxl).trans (mul_le_mul_of_nonneg_right hx1 hy)))
    · rcases le_total 0 xh with hxh | hxh
      -- xh*yl ≤ xh*y ≤ x*y
      · exact min_le_of_right_le (min_le_of_left_le
          ((mul_le_mul_of_nonneg_left hy1 hxh).trans (mul_le_mul_of_nonpos_right hx2 hy)))
      -- xh*yh ≤ xh*y ≤ x*y
      · exact min_le_of_right_le (min_le_of_right_le
          ((mul_le_mul_of_nonpos_left hy2 hxh).trans (mul_le_mul_of_nonpos_right hx2 hy)))
  · rcases le_total 0 y with hy | hy
    · rcases le_total 0 xh with hxh | hxh
      -- x*y ≤ xh*y ≤ xh*yh
      · exact le_max_of_le_right (le_max_of_le_right
          ((mul_le_mul_of_nonneg_right hx2 hy).trans (mul_le_mul_of_nonneg_left hy2 hxh)))
      -- x*y ≤ xh*y ≤ xh*yl
      · exact le_max_of_le_right (le_max_of_le_left
          ((mul_le_mul_of_nonneg_right hx2 hy).trans (mul_le_mul_of_nonpos_left hy1 hxh)))
    · rcases le_total 0 xl with hxl | hxl
      -- x*y ≤ xl*y ≤ xl*yh
      · exact le_max_of_le_left (le_max_of_le_right
          ((mul_le_mul_of_nonpos_right hx1 hy).trans (mul_le_mul_of_nonneg_left hy2 hxl)))
      -- x*y ≤ xl*y ≤ xl*yl
      · exact le_max_of_le_left (le_max_of_le_left
          ((mul_le_mul_of_nonpos_right hx1 hy).trans (mul_le_mul_of_nonpos_left hy1 hxl)))

/-- Sign-aware interval multiplication (§14.7 step 1).

Correct even when an interval straddles zero, which the §7.2 monotonic shortcut
is not. -/
def mulGeneral (a : Enclosure x) (b : Enclosure y) : Enclosure (x * y) where
  lo := min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
  hi := max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))
  lo_le := by
    push_cast
    exact (mul_mem_endpoints a.lo_le a.le_hi b.lo_le b.le_hi).1
  le_hi := by
    push_cast
    exact (mul_mem_endpoints a.lo_le a.le_hi b.lo_le b.le_hi).2

/-- Quotient of a nonnegative enclosure by a strictly positive one (§7.2).

The direction reverses on the divisor, which is why the hypotheses are stated on
the *endpoints* rather than on the enclosed reals: they are what the checker can
actually validate. -/
def divPos (a : Enclosure x) (b : Enclosure y) (ha : 0 ≤ a.lo) (hb : 0 < b.lo) :
    Enclosure (x / y) where
  lo := a.lo / b.hi
  hi := a.hi / b.lo
  lo_le := by
    have hblo : (0 : ℝ) < (b.lo : ℝ) := by exact_mod_cast hb
    have hy : (0 : ℝ) < y := lt_of_lt_of_le hblo b.lo_le
    have hbhi : (0 : ℝ) < (b.hi : ℝ) := lt_of_lt_of_le hy b.le_hi
    have halo : (0 : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast ha
    push_cast
    rw [div_le_div_iff₀ hbhi hy]
    have h1 : (a.lo : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right a.lo_le hy.le
    have h2 : (a.lo : ℝ) * y ≤ (a.lo : ℝ) * (b.hi : ℝ) :=
      mul_le_mul_of_nonneg_left b.le_hi halo
    nlinarith [a.lo_le, b.le_hi, halo, hy, hbhi]
  le_hi := by
    have hblo : (0 : ℝ) < (b.lo : ℝ) := by exact_mod_cast hb
    have hy : (0 : ℝ) < y := lt_of_lt_of_le hblo b.lo_le
    have halo : (0 : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast ha
    have hx : (0 : ℝ) ≤ x := le_trans halo a.lo_le
    push_cast
    rw [div_le_div_iff₀ hy hblo]
    nlinarith [a.le_hi, b.lo_le, hx, hy, hblo]

/-- Extract the directed lower bound (§7.1). -/
def lower (a : Enclosure x) : LowerBound x := ⟨a.lo, a.lo_le⟩

/-- Extract the directed upper bound (§7.1). -/
def upper (a : Enclosure x) : UpperBound x := ⟨a.hi, a.le_hi⟩

end Enclosure

end MatrixMath.Numeric
