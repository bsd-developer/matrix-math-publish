# ADR 0002 — Trust model and certification profiles

- Status: accepted
- Spec version: 2.1.0
- Supersedes: none

## Context

Spec §3 separates two things that are routinely conflated: the **logical axioms**
a theorem depends on, and the **external software** trusted to have computed the
result. §3.4 defines three labels — CK, CN, and XC — and §15.1 forbids reporting
XC as certified.

An implementation detail decides which profile is reachable. Lean's kernel
reduces structural recursion but not well-founded recursion or compiled `Array`
primitives. A checker written in the obvious way is therefore CN-only, and the
reason is invisible in the source.

## Decision

- **CK is the default target; CN is the documented fallback for large
  certificates.** `mm prove --profile ck` is expected to succeed for every
  version 1 Track B fixture.
- The executable checker is written to **reduce in the kernel**:
  - concrete factors are `List R`, not `Array R`;
  - the reconstruction check uses `List.range` and `List.all`, not a bounded
    `∀` quantifier, because `Nat.decidableBallLT` is defined by well-founded
    recursion.
  Both choices are recorded in the module documentation so a later refactor
  cannot silently downgrade every published result to CN.
- The axiom policy is enforced mechanically by `mm prove`, which parses
  `#print axioms` output, **reassembling Lean's line-wrapped axiom lists** before
  matching. CK permits only `propext`, `Classical.choice`, and `Quot.sound`; CN
  permits those plus exactly one `native_decide` axiom; `sorryAx` and any other
  project axiom fail the run.
- Lean kernel soundness is recorded in the **TCB ledger**, never in the axiom
  list, and is never labelled `A2` (§3.2).
- The Rust checker's agreement is reported as a cross-check and is never the
  basis for a certification label.

## Consequences

- Measured on this machine: Strassen over `ℤ` reaches CK in under a second, the
  23-term `T₃` over `𝔽₂` in 15 s, and the 47-term `T₄` over `𝔽₂` in 65 s.
- **`Z` and `Fp` reach CK; `Q` and `Qi` are CN-only.** The reason is specific and
  external: Lean core's `Rat` arithmetic is opaque to the kernel, so `decide`
  gets stuck on the first coefficient product. `Nat.gcd` and `Int` arithmetic
  both reduce fine, so this is a property of the `Rat` implementation rather than
  of the checker. `mm prove --profile ck` therefore rejects a `Q` or `Qi`
  certificate up front with that explanation instead of surfacing a raw Lean
  error.
- The route to CK for `Q` and `Qi`, if it is ever wanted, is to have the checker
  verify a **denominator-cleared integer identity** — scale each factor to be
  integral, carry the per-term integer multiplier and a common denominator `D`,
  and check `Σ_r c_r · ũ_r ⊗ ṽ_r ⊗ w̃_r = D · T` over `ℤ` — and then prove in `ℚ`
  that this implies the rational reconstruction. Only kernel *evaluation* is
  blocked; *reasoning* about `ℚ` is unaffected, so the proof side is ordinary
  Mathlib work. This is recorded as the known path, not as work in progress: the
  frontier Track B results are over `𝔽₂` and already reach CK.
- Keeping CK reachable costs performance: `List.getD` is linear, so the checker
  is asymptotically worse than an array implementation. §17.4 accepts that until
  a benchmark shows it matters, and any optimization must keep a reference
  comparison test.
- A future contributor who "modernizes" the representation to `Array` will find
  every CK proof fails, which is the intended failure mode.

## Rejected alternatives

- **`native_decide` everywhere.** Simpler and much faster. Rejected because it
  puts the Lean compiler, runtime, and native bigint implementation into the TCB
  of every result (§3.6) for no benefit at current sizes.
- **A hand-written kernel-friendly decision procedure per ring.** Rejected as
  premature: the generic `List`-based checker already reaches CK at `T₄` scale.
- **Reporting XC results with a caveat.** Rejected outright by §3.4 and §15.1.
