# ADR 0028: Stack-safe sums and shared exact logarithm arithmetic

Status: accepted for the isolated performance implementation; not adopted by the
concurrent frozen certification attempt. Spec2.1.0 mathematical semantics remain
unchanged.

2026-09-30 integration: the completed optimized baseline and improved local CN
proofs, their strict compiled/TCB audits and independent empty-store replays are
now preserved in the local results catalog. The user authorizes adoption of this
implementation into main under experiment0183. Those completed proofs retain
their frozen source identities; adoption does not certify the new main source.
The isolated measurements and earlier attempt descriptions below are historical.

## Context

The first full level-four CN attempt exhausted the Lean interpreter stack in a
large mapped rational sum after14570.876seconds. It did not return a false
inequality verdict. The exact certificate and numerical search findings remain
unchanged. Entropy evaluation also repeats the same precision-only ln(2)
enclosures, and block validation separately computes both logarithm endpoints.

## Decision

Retain the readable mathematical expressions and use kernel-proved function
equalities as compiler simplifications. Replace the lower/upper entropy sums and
the two giant leaf/level-two outer sums by left folds over exact rationals.
Hoist ln(2) bounds outside each fold. Keep empty entropy lists immediate. For
level-two entropy, compute the repeated mu term once. For maximum-entropy block
validation, share the mantissa, exponent, series length, partial sum and constant
ln(2) enclosures between lower/upper endpoints. Preserve all original guards,
precision rules, malformed-input verdicts, directions, and complete data.

All equalities quantify over arbitrary inputs, not just well-formed certificates.
They introduce no project axiom or residual assumption. Exact associativity
justifies the fold change; no floating-point arithmetic enters the checker.

## Consequences

The isolated matched diagnostic pilot on the exact first six root blocks measured
median1.0597s versus0.6313s for their block validation and0.3536s versus0.2555s for
entropy lower sums of their918 y-values. Three alternating trials followed a
warmup. These are small phase measurements, not full-proof speed claims.
The parser's duplicate-GCD candidate was also proved equivalent but showed no
meaningful speedup on8192 sampled rationals, so it is not integrated.

Evidence lives in the isolated ignored directory
`data/analysis/proof-performance/`; it includes source/input hashes, full output,
resource telemetry and retained failed/invalid attempts. The two initial phase
timers were invalid and excluded: one evaluated eagerly before timing, and the
second allowed optimization across clocks. The valid timer stores the result in
an IO reference before reading the end clock and uses a noinline boundary.

The running main proof remains frozen. Adoption requires a new source-bound
attempt and full CN, assurance/TCB audit and replay of the unchanged certificate.
No certification, exponent, milestone completion or full performance claim follows
from these isolated improvements. Native precompilation is not enabled here;
its large uncached Mathlib native dependency closure requires a separate plan.

## Rejected alternatives

Increasing the interpreter stack alone preserves the current attempt but leaves
non-tail recursion and repeated work. Skipping data, reducing precision, trusting
precomputed logarithms, changing the witness, or treating sample checks as full
certification are forbidden. A global mutable cache adds unnecessary complexity;
local immutable sharing suffices for these measured cases.
