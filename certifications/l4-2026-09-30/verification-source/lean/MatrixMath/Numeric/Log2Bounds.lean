import MatrixMath.Numeric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Log

/-!
# Proved directed logarithm bounds

Normative source: `docs/specs/0001_spec.md` §7.3, §14.7, as amended by
`docs/specs/0002_spec.md` §3.

§7.3 fixes the construction:

```text
x = m * 2^e exactly with m in [1,2)
z = (m-1)/(m+1)
log2(m) = (2 / ln 2) * artanh(z)
artanh(z) = sum_{k>=0} z^(2k+1)/(2k+1)
tail after N terms <= z^(2N+1) / ((2N+1)(1-z^2))
ln 2 = 2 * artanh(1/3)
```

Everything below is exact rational arithmetic carrying a proof about the real
quantity. `precision` selects the series length through `seriesLength`
(`0002_spec.md` L3); the certificate never supplies a trusted iteration count
(§7.3, `0002_spec.md` §3.5). No directed function below is indexed by a raw term
count: `logPartial`, `logTailBound`, and their two general lemmas are private
helpers feeding `seriesLength_tail_le`, and every exported bound takes a
precision.

Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one` states exactly this series in
the form `2/(2k+1) * z^(2k+1)` summing to `log (1+z) - log (1-z)`, which is
`2 * artanh z`. Working with that form directly avoids restating it.
-/

namespace MatrixMath.Numeric

open Finset

/-- One term of the `log` series: `2/(2k+1) * z^(2k+1)` (§7.3). -/
def logTerm (z : ℚ) (k : ℕ) : ℚ := 2 / (2 * k + 1) * z ^ (2 * k + 1)

/-- The partial sum of the first `n` terms (§7.3). -/
def logPartial (z : ℚ) (n : ℕ) : ℚ := ∑ k ∈ range n, logTerm z k

/-- The proved tail bound after `n` retained terms (§7.3).

`2 * z^(2n+1) / ((2n+1)(1 - z^2))` majorizes `∑_{k≥n} 2/(2k+1) z^(2k+1)` because
every retained denominator is at least `2n+1` and the remaining powers form a
geometric series in `z^2`. -/
def logTailBound (z : ℚ) (n : ℕ) : ℚ :=
  2 * z ^ (2 * n + 1) / ((2 * n + 1) * (1 - z ^ 2))

section Series

variable {z : ℚ}

private theorem cast_abs_lt_one (h0 : 0 ≤ z) (h1 : z < 1) : |(z : ℝ)| < 1 := by
  rw [abs_of_nonneg (by exact_mod_cast h0)]
  exact_mod_cast h1

private theorem term_cast (k : ℕ) :
    ((logTerm z k : ℚ) : ℝ) = 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1) := by
  unfold logTerm
  push_cast
  ring

private theorem term_nonneg (h0 : 0 ≤ z) (k : ℕ) :
    (0 : ℝ) ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1) := by
  have hz : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h0
  positivity

/-- The partial sum never exceeds the true logarithm: every retained term is
nonnegative for `0 ≤ z < 1` (§7.3). -/
theorem logPartial_le (h0 : 0 ≤ z) (h1 : z < 1) (n : ℕ) :
    ((logPartial z n : ℚ) : ℝ) ≤ Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ)) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (cast_abs_lt_one h0 h1)
  have hcast : ((logPartial z n : ℚ) : ℝ)
      = ∑ k ∈ range n, 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1) := by
    unfold logPartial
    push_cast
    exact Finset.sum_congr rfl fun k _ => term_cast k
  rw [hcast]
  exact sum_le_hasSum _ (fun k _ => term_nonneg h0 k) hs

/-- The tail after `n` retained terms is majorized by a geometric series, giving
the §7.3 bound `2 z^(2n+1) / ((2n+1)(1 - z^2))`. -/
theorem le_logPartial_add_tail (h0 : 0 ≤ z) (h1 : z < 1) (n : ℕ) :
    Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ))
      ≤ ((logPartial z n : ℚ) : ℝ) + ((logTailBound z n : ℚ) : ℝ) := by
  have hz : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h0
  have hz1 : (z : ℝ) < 1 := by exact_mod_cast h1
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1) with hf
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (cast_abs_lt_one h0 h1)
  have hsum : Summable f := hs.summable
  -- The geometric majorant for the tail.
  set c : ℝ := 2 * (1 / (2 * (n : ℝ) + 1)) * (z : ℝ) ^ (2 * n + 1) with hc
  set r : ℝ := (z : ℝ) ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr]
    nlinarith
  have hc0 : 0 ≤ c := by
    rw [hc]; positivity
  have hg : Summable (fun i : ℕ => c * r ^ i) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have htail_summable : Summable (fun i : ℕ => f (i + n)) :=
    (summable_nat_add_iff n).mpr hsum
  have hle : ∀ i : ℕ, f (i + n) ≤ c * r ^ i := by
    intro i
    have hpow : (z : ℝ) ^ (2 * (i + n) + 1) = (z : ℝ) ^ (2 * n + 1) * r ^ i := by
      rw [hr, ← pow_mul, ← pow_add]
      congr 1
      ring
    have hden : (1 : ℝ) / (2 * ((i : ℝ) + (n : ℝ)) + 1) ≤ 1 / (2 * (n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
    have hnn : (0 : ℝ) ≤ (z : ℝ) ^ (2 * n + 1) * r ^ i := by positivity
    calc f (i + n)
        = 2 * (1 / (2 * ((i : ℝ) + (n : ℝ)) + 1)) * ((z : ℝ) ^ (2 * n + 1) * r ^ i) := by
          rw [hf]
          push_cast
          rw [hpow]
      _ ≤ 2 * (1 / (2 * (n : ℝ) + 1)) * ((z : ℝ) ^ (2 * n + 1) * r ^ i) := by
          apply mul_le_mul_of_nonneg_right _ hnn
          exact mul_le_mul_of_nonneg_left hden (by norm_num)
      _ = c * r ^ i := by rw [hc]; ring
  have hsplit : (∑ k ∈ range n, f k) + ∑' i, f (i + n) = Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ)) := by
    rw [hsum.sum_add_tsum_nat_add n, hs.tsum_eq]
  have hbound : ∑' i, f (i + n) ≤ ∑' i : ℕ, c * r ^ i :=
    Summable.tsum_mono htail_summable hg hle
  have hgeom : ∑' i : ℕ, c * r ^ i = c * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hpartial : ((logPartial z n : ℚ) : ℝ) = ∑ k ∈ range n, f k := by
    unfold logPartial
    push_cast
    exact Finset.sum_congr rfl fun k _ => term_cast k
  have htailcast : ((logTailBound z n : ℚ) : ℝ) = c * (1 - r)⁻¹ := by
    unfold logTailBound
    rw [hc, hr]
    have hne : ((2 : ℝ) * (n : ℝ) + 1) ≠ 0 := by positivity
    have hne2 : (1 : ℝ) - (z : ℝ) ^ 2 ≠ 0 := by
      have : (z : ℝ) ^ 2 < 1 := by nlinarith
      linarith
    push_cast
    field_simp
  rw [← hsplit, hpartial, htailcast]
  linarith [hbound, hgeom ▸ hbound]

end Series

/-! ## Series-length selection

`docs/specs/0002_spec.md` §3. §7.3 fixes the tail bound; that document fixes how
many terms a given precision buys, so that Lean, Rust, and Python retain the same
number of them. Retaining more is sound and was what this file did before; it
made the authoritative checker strictly tighter than its own cross-checks, which
is the divergence `just test-diff` exists to surface.
-/

/-- The §7.3 tail after `n` retained `artanh` terms (`0002_spec.md` L1).

This is the *undoubled* tail. `logTailBound` above bounds the doubled series
`log(1+z) - log(1-z)` that this file actually sums, and `logTailBound_eq` records
the factor of two between them. Selection is stated on `seriesTail`. -/
def seriesTail (z : ℚ) (n : ℕ) : ℚ := z ^ (2 * n + 1) / ((2 * n + 1) * (1 - z ^ 2))

theorem logTailBound_eq (z : ℚ) (n : ℕ) : logTailBound z n = 2 * seriesTail z n := by
  unfold logTailBound seriesTail
  ring

/-- The selection threshold `2^-(precision+3)` (`0002_spec.md` L2).

The three spare bits are the tolerance split one `log2` evaluation already pays
for: two series enclosures, a doubling, a reciprocal, and a product. -/
def seriesTarget (precision : ℕ) : ℚ := 1 / 2 ^ (precision + 3)

/-- The selection cap (`0002_spec.md` §2.3).

The largest length the supported precision range can demand is 1290, at `z = 1/3`
and `precision = 4096`. The cap is six times that and exists to make selection
total, not to bound normal operation. -/
def seriesCap : ℕ := 8192

/-- Fuel-bounded search for the least conforming length.

Structural recursion on the fuel keeps this total without any hypothesis on
`precision`; a numeric helper that diverges off the supported range is a
rejection path waiting to be reached (`0002_spec.md` §3.2). -/
def seriesLengthAux (z target : ℚ) : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n => if seriesTail z n ≤ target then n else seriesLengthAux z target fuel (n + 1)

/-- The least `n ≤ seriesCap` with `seriesTail z n ≤ seriesTarget precision`,
or `seriesCap` when no such `n` exists (`0002_spec.md` L3). -/
def seriesLength (z : ℚ) (precision : ℕ) : ℕ :=
  seriesLengthAux z (seriesTarget precision) seriesCap 0

theorem le_seriesLengthAux (z target : ℚ) :
    ∀ fuel n, n ≤ seriesLengthAux z target fuel n := by
  intro fuel
  induction fuel with
  | zero => intro n; exact le_refl n
  | succ f ih =>
    intro n
    simp only [seriesLengthAux]
    split
    · exact le_refl n
    · exact le_trans (Nat.le_succ n) (ih (n + 1))

theorem seriesLengthAux_le (z target : ℚ) :
    ∀ fuel n, seriesLengthAux z target fuel n ≤ n + fuel := by
  intro fuel
  induction fuel with
  | zero => intro n; exact le_refl n
  | succ f ih =>
    intro n
    simp only [seriesLengthAux]
    split
    · omega
    · have := ih (n + 1); omega

/-- The selected length never exceeds the cap. -/
theorem seriesLength_le_cap (z : ℚ) (precision : ℕ) : seriesLength z precision ≤ seriesCap := by
  have := seriesLengthAux_le z (seriesTarget precision) seriesCap 0
  simpa [seriesLength] using this

/-- If the tail meets the target somewhere within the fuel, the returned length
meets it. Stated over the whole fuel so that `seriesLength_tail_le` needs only
the cap case. -/
theorem seriesLengthAux_tail_le (z target : ℚ) :
    ∀ fuel n, seriesTail z (n + fuel) ≤ target →
      seriesTail z (seriesLengthAux z target fuel n) ≤ target := by
  intro fuel
  induction fuel with
  | zero => intro n h; simpa [seriesLengthAux] using h
  | succ f ih =>
    intro n h
    simp only [seriesLengthAux]
    split
    · assumption
    · refine ih (n + 1) ?_
      have hn : n + 1 + f = n + (f + 1) := by omega
      rw [hn]
      exact h

/-- A length whose test fails is never returned. -/
theorem lt_seriesLengthAux_of_not_le (z target : ℚ) (fuel n : ℕ)
    (h : ¬ (seriesTail z n ≤ target)) (hfuel : 0 < fuel) :
    n < seriesLengthAux z target fuel n := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [seriesLengthAux, if_neg h]
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (le_seriesLengthAux z target f (n + 1))

/-- At the cap the tail is already far below every target the supported range
asks for: `seriesTail z 8192 ≤ 3^-16385` for `z ≤ 1/3`, against a threshold no
smaller than `2^-4099`. -/
theorem seriesTail_cap_le {z : ℚ} (hz0 : 0 ≤ z) (hz3 : z ≤ 1/3)
    {precision : ℕ} (hp : precision ≤ 4096) :
    seriesTail z seriesCap ≤ seriesTarget precision := by
  have hz2 : z ^ 2 ≤ 1/9 := by nlinarith
  have hden : (1 : ℚ) ≤ (2 * (seriesCap : ℚ) + 1) * (1 - z ^ 2) := by
    have hcap : ((seriesCap : ℕ) : ℚ) = 8192 := by norm_num [seriesCap]
    rw [hcap]
    nlinarith
  have hnum : (0 : ℚ) ≤ z ^ (2 * seriesCap + 1) := pow_nonneg hz0 _
  have hstep : seriesTail z seriesCap ≤ z ^ (2 * seriesCap + 1) := by
    unfold seriesTail
    exact div_le_self hnum hden
  have hpow : z ^ (2 * seriesCap + 1) ≤ (1/3 : ℚ) ^ (2 * seriesCap + 1) :=
    pow_le_pow_left₀ hz0 hz3 _
  have hhalf : (1/3 : ℚ) ^ (2 * seriesCap + 1) ≤ (1/2 : ℚ) ^ (2 * seriesCap + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hexp : precision + 3 ≤ 2 * seriesCap + 1 := by
    have : seriesCap = 8192 := rfl
    omega
  have hmono : (1/2 : ℚ) ^ (2 * seriesCap + 1) ≤ (1/2 : ℚ) ^ (precision + 3) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  have htarget : (1/2 : ℚ) ^ (precision + 3) = seriesTarget precision := by
    unfold seriesTarget
    rw [div_pow]
    norm_num
  linarith [hstep, hpow, hhalf, hmono, htarget ▸ hmono]

/-- **The selected length meets the threshold** (`0002_spec.md` L4).

Stated for every `precision ≤ 4096`; `0002_spec.md` §3.3 asks only for
`32 ≤ precision ≤ 4096`, and the lower bound is not needed. -/
theorem seriesLength_tail_le {z : ℚ} (hz0 : 0 ≤ z) (hz3 : z ≤ 1/3)
    {precision : ℕ} (hp : precision ≤ 4096) :
    seriesTail z (seriesLength z precision) ≤ seriesTarget precision := by
  unfold seriesLength
  refine seriesLengthAux_tail_le z (seriesTarget precision) seriesCap 0 ?_
  simpa using seriesTail_cap_le hz0 hz3 hp

/-- **The `ln 2` series always retains at least one term**
(`0002_spec.md` §3.3, property 2).

`seriesTail (1/3) 0 = 3/8`, and the threshold is at most `2^-3 = 1/8` at every
precision, so the first test always fails. This is what keeps the `log 2` lower
endpoint strictly positive so §7.2 can divide by it, replacing the `n + 1` shift
this file used to carry. -/
theorem one_le_seriesLength_third (precision : ℕ) : 1 ≤ seriesLength (1/3 : ℚ) precision := by
  have hzero : seriesTail (1/3 : ℚ) 0 = 3/8 := by norm_num [seriesTail]
  have hle : seriesTarget precision ≤ 1/8 := by
    unfold seriesTarget
    have h8 : (8 : ℚ) ≤ (2 : ℚ) ^ (precision + 3) := by
      calc (8 : ℚ) = (2 : ℚ) ^ 3 := by norm_num
        _ ≤ (2 : ℚ) ^ (precision + 3) := by
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : (1 : ℚ) / (2 : ℚ) ^ (precision + 3) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) h8
    simpa using this
  have hne : ¬ (seriesTail (1/3 : ℚ) 0 ≤ seriesTarget precision) := by
    rw [hzero]
    intro h
    linarith
  have := lt_seriesLengthAux_of_not_le (1/3 : ℚ) (seriesTarget precision) seriesCap 0 hne
    (by norm_num [seriesCap])
  show 0 < seriesLengthAux (1/3 : ℚ) (seriesTarget precision) seriesCap 0
  exact this


/-- The proved enclosure of `log (1+z) - log (1-z)` for `0 ≤ z < 1` (§7.3). -/
def logSeriesEnclosure (z : ℚ) (h0 : 0 ≤ z) (h1 : z < 1) (n : ℕ) :
    Enclosure (Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ))) where
  lo := logPartial z n
  hi := logPartial z n + logTailBound z n
  lo_le := logPartial_le h0 h1 n
  le_hi := by
    have := le_logPartial_add_tail h0 h1 n
    push_cast
    push_cast at this
    linarith

/-! ## From the series to `log` and `logb` -/

section Mantissa

variable {m : ℚ}

/-- The series variable `z = (m-1)/(m+1)` of §7.3. -/
def seriesVar (m : ℚ) : ℚ := (m - 1) / (m + 1)

theorem seriesVar_nonneg (h1 : 1 ≤ m) : 0 ≤ seriesVar m := by
  unfold seriesVar
  exact div_nonneg (by linarith) (by linarith)

theorem seriesVar_lt_one (h1 : 1 ≤ m) : seriesVar m < 1 := by
  unfold seriesVar
  have hpos : (0 : ℚ) < m + 1 := by linarith
  rw [div_lt_one hpos]
  linarith

/-- `(1+z)/(1-z) = m`, which turns the series into `log m` (§7.3). -/
theorem seriesVar_ratio (h1 : 1 ≤ m) :
    (1 + (seriesVar m : ℝ)) / (1 - (seriesVar m : ℝ)) = (m : ℝ) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  unfold seriesVar
  push_cast
  field_simp
  ring

/-! ## The executable directed API

`Enclosure` is proof-carrying, so its type index mentions `Real.log` and Lean
will not compile it. The checker therefore computes with plain rational
functions, and each carries a spec theorem naming the real quantity it bounds.
That keeps §7.1's requirement — direction visible in the API — while leaving the
evaluator executable: `log2Lower` and `log2Upper` are separate names with
separate theorems, and there is no ambiguous `log2`.
-/

/-- Every retained series term is nonnegative and the first is strictly positive,
so a nonempty partial sum is strictly positive. This is what makes the `log 2`
lower endpoint usable as a divisor (§7.2). -/
theorem logPartial_pos {z : ℚ} (hz : 0 < z) {k : ℕ} (hk : 1 ≤ k) : 0 < logPartial z k := by
  unfold logPartial
  refine Finset.sum_pos' (fun i _ => ?_) ⟨0, Finset.mem_range.mpr hk, ?_⟩
  · unfold logTerm
    have hp : (0 : ℚ) ≤ z ^ (2 * i + 1) := by positivity
    positivity
  · unfold logTerm
    norm_num
    exact hz

/-- The series length one `log m` evaluation retains at `precision`
(`0002_spec.md` L3). The `ln 2` series is the `m = 2` case of the same rule, so
the two lengths inside one `log2` evaluation differ in general and neither is
reused for the other. -/
def logTerms (m : ℚ) (precision : ℕ) : ℕ := seriesLength (seriesVar m) precision

/-- `log m` lower bound for `1 ≤ m`, from the retained series terms (§7.3). -/
def logLower (m : ℚ) (precision : ℕ) : ℚ := logPartial (seriesVar m) (logTerms m precision)

/-- `log m` upper bound for `1 ≤ m`, partial sum plus the proved tail (§7.3). -/
def logUpper (m : ℚ) (precision : ℕ) : ℚ :=
  logPartial (seriesVar m) (logTerms m precision) + logTailBound (seriesVar m) (logTerms m precision)

theorem logLower_le (h1 : 1 ≤ m) (precision : ℕ) :
    ((logLower m precision : ℚ) : ℝ) ≤ Real.log (m : ℝ) := by
  have hz0 := seriesVar_nonneg h1
  have hz1 := seriesVar_lt_one h1
  have hz0' : (0 : ℝ) ≤ ((seriesVar m : ℚ) : ℝ) := by exact_mod_cast hz0
  have hz1' : ((seriesVar m : ℚ) : ℝ) < 1 := by exact_mod_cast hz1
  have hnum : (1 : ℝ) + ((seriesVar m : ℚ) : ℝ) ≠ 0 := by linarith
  have hden : (1 : ℝ) - ((seriesVar m : ℚ) : ℝ) ≠ 0 := by linarith
  have hlog : Real.log (m : ℝ)
      = Real.log (1 + ((seriesVar m : ℚ) : ℝ)) - Real.log (1 - ((seriesVar m : ℚ) : ℝ)) := by
    rw [← Real.log_div hnum hden, seriesVar_ratio h1]
  rw [hlog]
  exact logPartial_le hz0 hz1 _

theorem le_logUpper (h1 : 1 ≤ m) (precision : ℕ) :
    Real.log (m : ℝ) ≤ ((logUpper m precision : ℚ) : ℝ) := by
  have hz0 := seriesVar_nonneg h1
  have hz1 := seriesVar_lt_one h1
  have hz0' : (0 : ℝ) ≤ ((seriesVar m : ℚ) : ℝ) := by exact_mod_cast hz0
  have hz1' : ((seriesVar m : ℚ) : ℝ) < 1 := by exact_mod_cast hz1
  have hnum : (1 : ℝ) + ((seriesVar m : ℚ) : ℝ) ≠ 0 := by linarith
  have hden : (1 : ℝ) - ((seriesVar m : ℚ) : ℝ) ≠ 0 := by linarith
  have hlog : Real.log (m : ℝ)
      = Real.log (1 + ((seriesVar m : ℚ) : ℝ)) - Real.log (1 - ((seriesVar m : ℚ) : ℝ)) := by
    rw [← Real.log_div hnum hden, seriesVar_ratio h1]
  rw [hlog]
  have := le_logPartial_add_tail hz0 hz1 (logTerms m precision)
  unfold logUpper
  push_cast
  push_cast at this
  linarith

/-! ### `log 2` -/

/-- The lower bound for `log 2`; `seriesVar 2 = 1/3`, so this is the §7.3
`ln 2 = 2 artanh(1/3)` series at the length `seriesLength` selects for `1/3`. -/
def logTwoLower (precision : ℕ) : ℚ := logLower 2 precision

/-- The upper bound for `log 2`. -/
def logTwoUpper (precision : ℕ) : ℚ := logUpper 2 precision

theorem seriesVar_two : seriesVar 2 = (1/3 : ℚ) := by norm_num [seriesVar]

theorem logTwoLower_pos (precision : ℕ) : 0 < logTwoLower precision := by
  unfold logTwoLower logLower logTerms
  rw [seriesVar_two]
  exact logPartial_pos (by norm_num) (one_le_seriesLength_third precision)

theorem logTwoLower_le (precision : ℕ) : ((logTwoLower precision : ℚ) : ℝ) ≤ Real.log 2 := by
  have := logLower_le (m := 2) (by norm_num) precision
  simpa [logTwoLower] using this

theorem le_logTwoUpper (precision : ℕ) : Real.log 2 ≤ ((logTwoUpper precision : ℚ) : ℝ) := by
  have := le_logUpper (m := 2) (by norm_num) precision
  simpa [logTwoUpper] using this

/-! ### Normalization and `log2` (§7.3) -/

/-- The binary exponent `e` with `2^e ≤ x < 2^(e+1)` (§7.3). -/
def binExp (x : ℚ) : ℤ := Int.log 2 x

/-- The mantissa `m = x / 2^e`, which lies in `[1,2)` for positive `x` (§7.3). -/
def mantissa (x : ℚ) : ℚ := x / (2 : ℚ) ^ (binExp x)

theorem two_zpow_pos (e : ℤ) : (0 : ℚ) < (2 : ℚ) ^ e := by positivity

theorem one_le_mantissa {x : ℚ} (hx : 0 < x) : 1 ≤ mantissa x := by
  have h := Int.zpow_log_le_self (b := 2) (r := x) (by norm_num) hx
  have hp := two_zpow_pos (binExp x)
  unfold mantissa binExp
  rw [le_div_iff₀ (by exact_mod_cast hp)]
  simpa using h

theorem mantissa_lt_two {x : ℚ} (hx : 0 < x) : mantissa x < 2 := by
  have h := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
  have hp := two_zpow_pos (binExp x)
  unfold mantissa binExp
  rw [div_lt_iff₀ (by exact_mod_cast hp)]
  calc x < (2 : ℚ) ^ (Int.log 2 x + 1) := by simpa using h
    _ = 2 * (2 : ℚ) ^ (Int.log 2 x) := by rw [zpow_add_one₀ (by norm_num)]; ring

theorem mantissa_spec {x : ℚ} (hx : 0 < x) :
    (x : ℝ) = ((mantissa x : ℚ) : ℝ) * (2 : ℝ) ^ (binExp x) := by
  have hp := two_zpow_pos (binExp x)
  unfold mantissa
  push_cast
  field_simp

/-! ## Outward dyadic rounding (ADR 0011, `0011_spec.md`)

Every produced `log2` bound is snapped outward onto the shared
`2^-(precision+32)` grid — a lower bound floors, an upper bound ceils — so
that downstream accumulations are shift-and-adds on bounded denominators
instead of sums over pairwise-coprime series denominators. Soundness is one
line per direction: flooring can only lower a lower bound, ceiling can only
raise an upper bound, so every §7.2 propagation rule composes unchanged. -/

/-- The rounding grid width: `precision + 32` spare bits, matching the Rust
evaluators (`mm-rat/src/log2.rs`) and the ADR 0011 error budget under which
`0004_spec.md` P1's `tol(precision) = 2^-precision` holds unamended. -/
def roundingBits (precision : ℕ) : ℕ := precision + 32

/-- Floor onto the `2^-bits` grid: the outward direction for a lower bound. -/
def floorDyadic (x : ℚ) (bits : ℕ) : ℚ := ⌊x * 2 ^ bits⌋ / 2 ^ bits

/-- Ceiling onto the `2^-bits` grid: the outward direction for an upper bound. -/
def ceilDyadic (x : ℚ) (bits : ℕ) : ℚ := ⌈x * 2 ^ bits⌉ / 2 ^ bits

theorem floorDyadic_le (x : ℚ) (bits : ℕ) : floorDyadic x bits ≤ x := by
  unfold floorDyadic
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ bits)]
  exact Int.floor_le _

theorem le_ceilDyadic (x : ℚ) (bits : ℕ) : x ≤ ceilDyadic x bits := by
  unfold ceilDyadic
  rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ bits)]
  exact Int.le_ceil _

/-- The unsnapped §7.3 lower bound; a private stage of `log2Lower`. -/
def log2LowerRaw (x : ℚ) (precision : ℕ) : ℚ :=
  logLower (mantissa x) precision / logTwoUpper precision + (binExp x : ℚ)

/-- The unsnapped §7.3 upper bound; a private stage of `log2Upper`. -/
def log2UpperRaw (x : ℚ) (precision : ℕ) : ℚ :=
  logUpper (mantissa x) precision / logTwoLower precision + (binExp x : ℚ)

/-- A value known to be at most `log2 x` (§7.3), snapped outward onto the
`2^-(precision+32)` grid (ADR 0011).

Direction is in the name; there is deliberately no ambiguous `log2`. -/
def log2Lower (x : ℚ) (precision : ℕ) : ℚ :=
  floorDyadic (log2LowerRaw x precision) (roundingBits precision)

/-- A value known to be at least `log2 x` (§7.3), snapped outward onto the
`2^-(precision+32)` grid (ADR 0011). -/
def log2Upper (x : ℚ) (precision : ℕ) : ℚ :=
  ceilDyadic (log2UpperRaw x precision) (roundingBits precision)

private theorem logb_split {x : ℚ} (hx : 0 < x) :
    Real.logb 2 (x : ℝ)
      = Real.log ((mantissa x : ℚ) : ℝ) / Real.log 2 + (binExp x : ℝ) := by
  have hlog2 : Real.log 2 ≠ 0 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  have hm : (0 : ℝ) < ((mantissa x : ℚ) : ℝ) := by
    have := one_le_mantissa hx
    have : (1 : ℝ) ≤ ((mantissa x : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  rw [Real.logb, mantissa_spec hx, Real.log_mul (ne_of_gt hm) (by positivity),
    Real.log_zpow]
  field_simp

/-- Soundness of the unsnapped lower stage (§7.3). -/
theorem log2LowerRaw_le {x : ℚ} (hx : 0 < x) (precision : ℕ) :
    ((log2LowerRaw x precision : ℚ) : ℝ) ≤ Real.logb 2 (x : ℝ) := by
  have hm1 := one_le_mantissa hx
  have hlow := logLower_le hm1 precision
  have hup2 := le_logTwoUpper precision
  have hlow2 := logTwoLower_le precision
  have hpos2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlo2pos : (0 : ℚ) < logTwoLower precision := logTwoLower_pos precision
  have hup2pos : (0 : ℝ) < ((logTwoUpper precision : ℚ) : ℝ) := lt_of_lt_of_le hpos2 hup2
  have hlognn : (0 : ℝ) ≤ Real.log ((mantissa x : ℚ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm1)
  rw [logb_split hx]
  unfold log2LowerRaw
  push_cast
  have hdiv : ((logLower (mantissa x) precision : ℚ) : ℝ) / ((logTwoUpper precision : ℚ) : ℝ)
      ≤ Real.log ((mantissa x : ℚ) : ℝ) / Real.log 2 := by
    rw [div_le_div_iff₀ hup2pos hpos2]
    nlinarith [hlow, hup2, hlognn, hpos2, hup2pos]
  linarith

/-- **Soundness of the lower bound** (§7.3, ADR 0011): the outward snap can
only lower a lower bound, so soundness composes in one step. -/
theorem log2Lower_le {x : ℚ} (hx : 0 < x) (precision : ℕ) :
    ((log2Lower x precision : ℚ) : ℝ) ≤ Real.logb 2 (x : ℝ) := by
  have hsnap : log2Lower x precision ≤ log2LowerRaw x precision :=
    floorDyadic_le _ _
  have hsnap' : ((log2Lower x precision : ℚ) : ℝ)
      ≤ ((log2LowerRaw x precision : ℚ) : ℝ) := by exact_mod_cast hsnap
  exact hsnap'.trans (log2LowerRaw_le hx precision)

/-- Soundness of the unsnapped upper stage (§7.3). -/
theorem le_log2UpperRaw {x : ℚ} (hx : 0 < x) (precision : ℕ) :
    Real.logb 2 (x : ℝ) ≤ ((log2UpperRaw x precision : ℚ) : ℝ) := by
  have hm1 := one_le_mantissa hx
  have hup := le_logUpper hm1 precision
  have hlow2 := logTwoLower_le precision
  have hpos2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlo2pos : (0 : ℚ) < logTwoLower precision := logTwoLower_pos precision
  have hlo2pos' : (0 : ℝ) < ((logTwoLower precision : ℚ) : ℝ) := by exact_mod_cast hlo2pos
  have hlognn : (0 : ℝ) ≤ Real.log ((mantissa x : ℚ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm1)
  rw [logb_split hx]
  unfold log2UpperRaw
  push_cast
  have hdiv : Real.log ((mantissa x : ℚ) : ℝ) / Real.log 2
      ≤ ((logUpper (mantissa x) precision : ℚ) : ℝ) / ((logTwoLower precision : ℚ) : ℝ) := by
    rw [div_le_div_iff₀ hpos2 hlo2pos']
    nlinarith [hup, hlow2, hlognn, hpos2, hlo2pos']
  linarith

/-- **Soundness of the upper bound** (§7.3, ADR 0011): the outward snap can
only raise an upper bound, so soundness composes in one step. -/
theorem le_log2Upper {x : ℚ} (hx : 0 < x) (precision : ℕ) :
    Real.logb 2 (x : ℝ) ≤ ((log2Upper x precision : ℚ) : ℝ) := by
  have hsnap : log2UpperRaw x precision ≤ log2Upper x precision :=
    le_ceilDyadic _ _
  have hsnap' : ((log2UpperRaw x precision : ℚ) : ℝ)
      ≤ ((log2Upper x precision : ℚ) : ℝ) := by exact_mod_cast hsnap
  exact (le_log2UpperRaw hx precision).trans hsnap'

end Mantissa

end MatrixMath.Numeric