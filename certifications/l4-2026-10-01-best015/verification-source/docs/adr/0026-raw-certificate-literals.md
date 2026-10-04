# ADR 0026 — Raw literals for complete certificate bytes

Status: accepted after experiments 0070 and 0073. Spec version: 2.1.0.

## Context

The full 0062 readiness payload passed Rust checking, but Lean overflowed its
default stack while parsing the generated escaped string. Experiment 0070
reproduced that failure and parsed the identical bytes as a raw string. The
separate 0073 diagnostic elaborated the complete raw `ByteArray` definition,
forced its constant evaluation and compared all 458,018,493 bytes to the
bound payload. It retained a compiled module. The original controller's
stdout/stderr classification error and the independently audited successful
scientific result are both preserved in
[the report](../experiments/0073-raw-constant-elaboration.md).

## Decision

Emit complete published certificate bytes in a Lean raw string for both the
general and symmetric generators. Use one more delimiter hash than the
longest consecutive hash run immediately following any quote in the payload.
This deterministic rule prevents a payload substring from closing the literal.
Reject invalid UTF-8, preserve every byte inside the literal, and retain the
ordinary `.toUTF8` conversion.

Keep complete Lean decoding, independent Rust checking, exact claim and digest
binding, the single native acceptance evaluation, certificate-specific theorem,
compiled assurance and existing axiom policy. This is a source representation
change, with no change to certificate semantics or mathematical assumptions.
Register a new complete CN readiness attempt separately under 0074.

## Consequences

The measured escape-specific parser failure is removed from the production
representation. Constant elaboration is measured, but full level-four Lean
checker evaluation remains unestablished until the ordinary CN attempt finishes.
The diagnostic and this generator change establish no exponent bound.

## Rejected alternatives

Increasing the native stack would retain a demonstrated avoidable parser cost.
Loading the payload from a file during the acceptance proof would change how
the closed theorem binds published evidence. Splitting or partially checking the
payload would require additional design and does not follow from these results.
