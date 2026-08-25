import MatrixMath.Numeric.Log2Bounds

/-!
# Proved directed entropy bounds

Normative source: `docs/specs/0001_spec.md` §7.3, §7.4, A.3, A.11 (A22).

Entropies are base two (Appendix A):

```text
H(rho) = - sum_{x in supp rho} rho(x) log2 rho(x)
```

with the explicit convention `0 * log 0 = 0` (§7.3). Mathlib defines
`Real.log 0 = 0`, so the real-valued definition needs no special case and the
executable bound — which skips zero entries — agrees with it definitionally.

Direction matters and is in the names: for positive `p` the term
`-p * log2 p` multiplies a logarithm by the **negative** factor `-p`, so a lower
bound on the entropy term comes from an *upper* bound on the logarithm (§7.3).
-/

namespace MatrixMath.Numeric

open Finset

/-- The real entropy term `-(p * log2 p)`, with `0 * log 0 = 0` (A.3, §7.3). -/
noncomputable def entropyTerm (p : ℝ) : ℝ := -(p * Real.logb 2 p)

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

/-- The real base-two entropy of a finite distribution (A.3). -/
noncomputable def entropy {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ a ∈ s, entropyTerm (p a)

/-- A value known to be at most `-(p * log2 p)` (§7.3).

The zero branch returns exactly zero and never invokes `log 0`. -/
def entropyTermLower (p : ℚ) (n : ℕ) : ℚ :=
  if 0 < p then -p * log2Upper p n else 0

/-- A value known to be at least `-(p * log2 p)` (§7.3). -/
def entropyTermUpper (p : ℚ) (n : ℕ) : ℚ :=
  if 0 < p then -p * log2Lower p n else 0

theorem entropyTermLower_le {p : ℚ} (hp : 0 ≤ p) (n : ℕ) :
    ((entropyTermLower p n : ℚ) : ℝ) ≤ entropyTerm ((p : ℚ) : ℝ) := by
  unfold entropyTermLower entropyTerm
  by_cases hpos : 0 < p
  · rw [if_pos hpos]
    have hp' : (0 : ℝ) < ((p : ℚ) : ℝ) := by exact_mod_cast hpos
    have hup := le_log2Upper hpos n
    push_cast
    nlinarith [hup, hp']
  · have : p = 0 := le_antisymm (not_lt.mp hpos) hp
    subst this
    simp

theorem le_entropyTermUpper {p : ℚ} (hp : 0 ≤ p) (n : ℕ) :
    entropyTerm ((p : ℚ) : ℝ) ≤ ((entropyTermUpper p n : ℚ) : ℝ) := by
  unfold entropyTermUpper entropyTerm
  by_cases hpos : 0 < p
  · rw [if_pos hpos]
    have hp' : (0 : ℝ) < ((p : ℚ) : ℝ) := by exact_mod_cast hpos
    have hlow := log2Lower_le hpos n
    push_cast
    nlinarith [hlow, hp']
  · have : p = 0 := le_antisymm (not_lt.mp hpos) hp
    subst this
    simp

/-- A value known to be at most `H(rho)` (§7.2, A.3). -/
def entropyLower {ι : Type*} (s : Finset ι) (p : ι → ℚ) (n : ℕ) : ℚ :=
  ∑ a ∈ s, entropyTermLower (p a) n

/-- A value known to be at least `H(rho)` (§7.2, A.3). -/
def entropyUpper {ι : Type*} (s : Finset ι) (p : ι → ℚ) (n : ℕ) : ℚ :=
  ∑ a ∈ s, entropyTermUpper (p a) n

theorem entropyLower_le {ι : Type*} {s : Finset ι} {p : ι → ℚ}
    (hp : ∀ a ∈ s, 0 ≤ p a) (n : ℕ) :
    ((entropyLower s p n : ℚ) : ℝ) ≤ entropy s (fun a => ((p a : ℚ) : ℝ)) := by
  unfold entropyLower entropy
  push_cast
  exact Finset.sum_le_sum fun a ha => entropyTermLower_le (hp a ha) n

theorem le_entropyUpper {ι : Type*} {s : Finset ι} {p : ι → ℚ}
    (hp : ∀ a ∈ s, 0 ≤ p a) (n : ℕ) :
    entropy s (fun a => ((p a : ℚ) : ℝ)) ≤ ((entropyUpper s p n : ℚ) : ℝ) := by
  unfold entropyUpper entropy
  push_cast
  exact Finset.sum_le_sum fun a ha => le_entropyTermUpper (hp a ha) n

/-! ## The maximum-entropy bound (A22)

§7.4 and A.11 fix the statement: for a strictly positive witness `y` matching
`rho`'s three marginals, with `|log2 y(a) - g(a)| <= eps` for the additive
`g(a) = lambda0 + lambda_X(a_X) + lambda_Y(a_Y) + lambda_Z(a_Z)`,

```text
H(y) <= H_D^max(rho) <= H(y) + 2 eps.
```

A.11 states that **no project axiom is permitted** for A22, so it is proved here
from Gibbs' inequality rather than assumed.

The additive structure of `g` enters only through the hypothesis that `rho` and
`y` give it the same expectation, which is exactly what equal marginals buy. That
keeps this lemma independent of the tree machinery: the Track A layer discharges
`expectation_eq` from marginal equality and applies the lemma unchanged.
-/

section MaxEntropy

variable {ι : Type*} {s : Finset ι} {y rho g : ι → ℝ} {ε : ℝ}

/-- Gibbs' inequality in base two, in the form the maximum-entropy bound needs.

Proved from `log x ≤ x - 1`, so it needs no convexity machinery. The `rho a = 0`
case is handled directly rather than by a limit, matching the `0 log 0 = 0`
convention of §7.3. -/
theorem sum_mul_logb_le
    (hy : ∀ a ∈ s, 0 < y a) (hr : ∀ a ∈ s, 0 ≤ rho a)
    (hsum : ∑ a ∈ s, y a ≤ ∑ a ∈ s, rho a) :
    ∑ a ∈ s, rho a * Real.logb 2 (y a) ≤ ∑ a ∈ s, rho a * Real.logb 2 (rho a) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Pointwise: rho a * (log (y a) - log (rho a)) ≤ y a - rho a.
  have hpoint : ∀ a ∈ s, rho a * (Real.log (y a) - Real.log (rho a)) ≤ y a - rho a := by
    intro a ha
    rcases eq_or_lt_of_le (hr a ha) with hzero | hpos
    · rw [← hzero]
      simp only [zero_mul]
      linarith [hy a ha, hzero]
    · have hya := hy a ha
      have hdiv : (0 : ℝ) < y a / rho a := div_pos hya hpos
      have hlog : Real.log (y a / rho a) ≤ y a / rho a - 1 :=
        Real.log_le_sub_one_of_pos hdiv
      rw [Real.log_div (ne_of_gt hya) (ne_of_gt hpos)] at hlog
      have := mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
      calc rho a * (Real.log (y a) - Real.log (rho a)) ≤ rho a * (y a / rho a - 1) := this
        _ = y a - rho a := by field_simp
  have hsummed : ∑ a ∈ s, rho a * (Real.log (y a) - Real.log (rho a))
      ≤ ∑ a ∈ s, (y a - rho a) := Finset.sum_le_sum hpoint
  rw [Finset.sum_sub_distrib] at hsummed
  have hzero : ∑ a ∈ s, rho a * (Real.log (y a) - Real.log (rho a)) ≤ 0 := by linarith
  have hexpand : ∑ a ∈ s, rho a * (Real.log (y a) - Real.log (rho a))
      = (∑ a ∈ s, rho a * Real.log (y a)) - ∑ a ∈ s, rho a * Real.log (rho a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hexpand] at hzero
  have hlogb : ∀ (f : ι → ℝ),
      ∑ a ∈ s, rho a * Real.logb 2 (f a) = (∑ a ∈ s, rho a * Real.log (f a)) / Real.log 2 := by
    intro f
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by rw [Real.logb]; ring
  rw [hlogb y, hlogb rho]
  exact (div_le_div_iff_of_pos_right hL).mpr (by linarith)

/-- **A22, the maximum-entropy upper bound.**

Any distribution `rho` that gives the additive function `g` the same expectation
as `y` — which equal marginals guarantee — has entropy at most `H(y) + 2 eps`.

Together with the trivial direction (`y` itself is feasible, so
`H(y) <= H_D^max(rho)`), this is A22. -/
theorem entropy_le_of_close
    (hy : ∀ a ∈ s, 0 < y a) (hysum : ∑ a ∈ s, y a = 1)
    (hr : ∀ a ∈ s, 0 ≤ rho a) (hrsum : ∑ a ∈ s, rho a = 1)
    (hexp : ∑ a ∈ s, rho a * g a = ∑ a ∈ s, y a * g a)
    (hclose : ∀ a ∈ s, |Real.logb 2 (y a) - g a| ≤ ε) :
    entropy s rho ≤ entropy s y + 2 * ε := by
  have hgibbs := sum_mul_logb_le hy hr (by rw [hysum, hrsum])
  -- rho-weighted: replacing log2 y by g costs at most eps.
  have hbound : ∀ (w : ι → ℝ), (∀ a ∈ s, 0 ≤ w a) → (∑ a ∈ s, w a = 1) →
      |(∑ a ∈ s, w a * Real.logb 2 (y a)) - ∑ a ∈ s, w a * g a| ≤ ε := by
    intro w hw hwsum
    have hstep : |∑ a ∈ s, w a * (Real.logb 2 (y a) - g a)| ≤ ∑ a ∈ s, w a * ε := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
      rw [abs_mul, abs_of_nonneg (hw a ha)]
      exact mul_le_mul_of_nonneg_left (hclose a ha) (hw a ha)
    rw [← Finset.sum_mul, hwsum, one_mul] at hstep
    have hsplit : ∑ a ∈ s, w a * (Real.logb 2 (y a) - g a)
        = (∑ a ∈ s, w a * Real.logb 2 (y a)) - ∑ a ∈ s, w a * g a := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rwa [hsplit] at hstep
  have hrho := hbound rho hr hrsum
  have hyy := hbound y (fun a ha => le_of_lt (hy a ha)) hysum
  have hrho' := abs_le.mp hrho
  have hyy' := abs_le.mp hyy
  unfold entropy entropyTerm
  have hneg : ∀ (f : ι → ℝ), ∑ a ∈ s, -(f a * Real.logb 2 (f a))
      = -∑ a ∈ s, f a * Real.logb 2 (f a) := by
    intro f
    rw [← Finset.sum_neg_distrib]
  rw [hneg rho, hneg y]
  linarith [hgibbs, hrho'.1, hrho'.2, hyy'.1, hyy'.2, hexp]

end MaxEntropy

end MatrixMath.Numeric

/-! ## Additive functions and marginals (A.11)

A22's hypothesis is that `ρ` and `y` give the additive `g` the same expectation.
§7.4 supplies that through equal marginals, and this is the step that connects
the two: an additive function's expectation depends on a distribution only
through its marginals.
-/

namespace MatrixMath.Numeric

open Finset

variable {ι κ : Type*} [DecidableEq κ]

/-- The fibrewise expansion of a composed weight: `∑_a p a · f (k a)` groups by
the value of `k`. -/
theorem sum_comp_eq_fiber (s : Finset ι) (t : Finset κ) (k : ι → κ)
    (hk : ∀ a ∈ s, k a ∈ t) (p : ι → ℝ) (f : κ → ℝ) [DecidableEq ι] :
    ∑ a ∈ s, p a * f (k a) = ∑ v ∈ t, f v * ∑ a ∈ s.filter (fun a => k a = v), p a := by
  rw [← Finset.sum_fiberwise_of_maps_to hk (fun a => p a * f (k a))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_filter] at ha
  rw [ha.2]
  ring

/-- **Equal marginals give an additive function equal expectation.**

This is what §7.4's marginal conditions buy, and it is exactly the hypothesis
`entropy_le_of_close` needs. -/
theorem sum_additive_of_marginals {s : Finset ι} [DecidableEq ι] {t : Finset κ}
    {kx ky kz : ι → κ} (hx : ∀ a ∈ s, kx a ∈ t) (hy : ∀ a ∈ s, ky a ∈ t)
    (hz : ∀ a ∈ s, kz a ∈ t) (l0 : ℝ) (lx ly lz : κ → ℝ) (p q : ι → ℝ)
    (hsum : ∑ a ∈ s, p a = ∑ a ∈ s, q a)
    (mx : ∀ v : κ, ∑ a ∈ s.filter (fun a => kx a = v), p a
                 = ∑ a ∈ s.filter (fun a => kx a = v), q a)
    (my : ∀ v : κ, ∑ a ∈ s.filter (fun a => ky a = v), p a
                 = ∑ a ∈ s.filter (fun a => ky a = v), q a)
    (mz : ∀ v : κ, ∑ a ∈ s.filter (fun a => kz a = v), p a
                 = ∑ a ∈ s.filter (fun a => kz a = v), q a) :
    ∑ a ∈ s, p a * (l0 + lx (kx a) + ly (ky a) + lz (kz a))
      = ∑ a ∈ s, q a * (l0 + lx (kx a) + ly (ky a) + lz (kz a)) := by
  have expand : ∀ w : ι → ℝ,
      ∑ a ∈ s, w a * (l0 + lx (kx a) + ly (ky a) + lz (kz a))
        = l0 * (∑ a ∈ s, w a) + (∑ a ∈ s, w a * lx (kx a))
          + (∑ a ∈ s, w a * ly (ky a)) + ∑ a ∈ s, w a * lz (kz a) := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- One coordinate at a time: expand fibrewise, then use that fibre's marginal
  -- equality.
  have ex : ∀ (k : ι → κ) (l : κ → ℝ), (∀ a ∈ s, k a ∈ t) →
      (∀ v : κ, ∑ a ∈ s.filter (fun a => k a = v), p a
              = ∑ a ∈ s.filter (fun a => k a = v), q a) →
      ∑ a ∈ s, p a * l (k a) = ∑ a ∈ s, q a * l (k a) := by
    intro k l hk m
    rw [sum_comp_eq_fiber s t k hk p l, sum_comp_eq_fiber s t k hk q l]
    exact Finset.sum_congr rfl fun v _ => by rw [m v]
  rw [expand p, expand q, hsum, ex kx lx hx mx, ex ky ly hy my, ex kz lz hz mz]

end MatrixMath.Numeric
