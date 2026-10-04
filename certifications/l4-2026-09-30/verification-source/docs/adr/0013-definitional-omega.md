# ADR 0013: `omegaExponent` is defined, not opaque

Status: accepted.

## Context

Version 1 declared `omegaExponent : ℝ` as an `opaque` constant and stated the
sole project axiom against it:

```lean
axiom AX1_combination_loss :
    ∀ {q levels : ℕ} {Ω : ℝ}, CombinationLossFeasible q levels Ω → omegaExponent ≤ Ω
```

An adversarial review of the paper draft
(`docs/notes/2026-08-24/paper-review-adjustments.md`, item 1) identified the
consequence: the kernel-accepted top-level theorems bound a real number about
which the development states nothing. The formal statement is satisfiable in a
model where `omegaExponent = 0`; the connection to matrix multiplication
lived entirely in prose. Unlike the laser method — whose formalization is a
deliberate non-goal (`0001_spec.md` §1.4) — the *definition* of the exponent
requires no combination-loss machinery at all.

## Decision

`MatrixMath.Spec.OmegaExponent` defines the exponent and `Axioms.lean` states
AX1 against the definition. Three choices, each the conservative direction:

1. **Field `ℚ`.** The cited theorem of Alman et al. holds over every field, so
   its `ℚ` specialization is a strictly weaker assertion — the axiom assumes
   less than the literature provides. `ℚ` also matches the certificates'
   arithmetic and needs no analysis to set up.

2. **Rank via Strassen normal form.** A `MulDecomposition n r` is `r`
   rank-one bilinear terms (`Mat n →ₗ[ℚ] ℚ` functional pairs with output
   matrices) summing to the product; `mulRank n` is `sInf` of the inhabited
   set of achievable `r`.

3. **The infimum characterization.**
   `omegaExponent = ⨅ (n ≥ 2), logb n (mulRank n)`. This equals the usual
   `inf { τ | R(n) = O(n^τ) }` by submultiplicativity of rank under tensor
   powers (classical; Bläser's survey, §Strassen). The equivalence is **not**
   formalized and is not needed: the definition itself is now the object the
   axiom speaks about, and it is the standard one.

Junk-value hygiene, proved in the module rather than assumed: the rank set is
inhabited (`mulRank_le_cube`, schoolbook `n³` decomposition, so `sInf` is
attained), ranks are positive (`one_le_mulRank`, so `logb` sees arguments
`≥ 1`), and the infimum range is nonempty and bounded below
(`omegaExponent_nonneg`). None of these lemmas enters any certificate
theorem's trust chain; they exist so the definition cannot be a junk-value
artifact of Mathlib's total functions.

## Consequences

- The statement of every generated `omegaResult_*` theorem now has
  mathematical content inside Lean: it bounds the defined exponent of
  rational matrix multiplication, not an opaque constant.
- AX1's text is unchanged; its meaning strengthens from "relates feasibility
  to some real" to the cited theorem's `ℚ` instance. The axiom count and the
  §3.2 admissible-axiom policy are unchanged; `#print axioms` output for
  existing generated modules is byte-identical.
- The definition adds no axioms (it is `noncomputable` via `Classical.choice`,
  already admitted) and nothing in the checker or decoder depends on it.
- The equivalence of the infimum characterization with the big-O form, and
  any field-change statement, remain non-goals; formalizing either would be
  new scope with its own ADR.
