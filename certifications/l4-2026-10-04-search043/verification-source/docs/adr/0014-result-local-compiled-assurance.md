# ADR 0014: Reuse exact witnesses and audit compiled omega results

Status: accepted.

## Context

The full level-four certificate pilot exhausted its 900-second production
budget without a certificate. Its empty logs did not identify the stage. The
producer constructed the same rational tree and maximum-entropy witnesses
twice, changing only the claimed omega after the independent exact evaluator
returned its minimum. A bounded block cache does not retain the full level-four
witness set.

The omega proof emitter already invokes a generic, closed Lean checker for
levels two through four. Its assurance record nevertheless described an
experimental level-two-only result and omitted the compiled declaration
statements and source bindings required by specification §4.6. Removing that
description alone would not establish assurance.

## Decision

1. Build the rational tree and witnesses once per precision attempt. After
   exact `omega-min`, copy the claim object, replace only `claim.omega`, and
   encode the canonical document again. This changes no rounding, witness,
   checker, or mathematical semantics. L2 and L3 fixtures compare the entire
   resulting byte sequence against the former second-build construction.
   Flushed JSON progress records identify deterministic stages and block/node
   milestones; elapsed time remains a supervisor measurement.

2. Every generated general or symmetric omega proof imports
   `MatrixMath.ResultAssurance` and calls it after both closed declarations
   elaborate. It queries their actual compiled statements and transitive
   axioms. The evaluation must use only standard axioms and one native axiom
   scoped to that evaluation declaration. The result must use the same native
   axiom and exactly the existing project axiom `AX1_combination_loss` in
   addition to standard axioms. The helper checks the native axiom's actual
   type is definitionally `decide <evaluation proposition> = true`; a matching
   name alone is insufficient. No new mathematical axiom is introduced.

3. Persist the exact compressed compiled query as `compiled-assurance.json`
   beside `assurance.json`. Bind the certificate, generated module, compiled
   query bytes, and handwritten Lean source closure by SHA-256. Statement
   hashes use the pinned Lean pretty-printer with explicit universes,
   arguments, and fully qualified names, matching the core assurance audit.
   Source closure uses its existing sorted-path, NUL, raw-file-digest recipe.
   Rebuild the proof's handwritten import closure before elaboration and reject
   any source or generated-module change during the operation. The Python
   supervisor independently verifies the structured rows and all bindings.

4. Mark the result-local assurance active, with no residual premises, only
   after the actual closed proof and compiled audit complete successfully.
   Report the claimed bound as an exact rational: truncating a decimal downward
   can misstate a stronger inequality than the theorem proves. The generic
   theorem, checker arithmetic, AX1 statement, and CN policy remain unchanged.

## Limits

This is result-local proof evidence, not publication completion. Report/release
integration, independent required verification, and durable artifact archiving
remain requirements for a published certified result. Neither producer progress
nor a numerical result establishes CN.

The raw general Lean beta recursion can expand a root-region mixture to
70,853,000 entries at level four. Repeated list indexing adds a separate
quadratic cost. A source-bound integer count audit is retained under
`data/analysis/l4-certification-readiness/`. Full L4 CN must wait for proved
equivalent evaluation improvements; this reporting change neither bypasses
that computation nor claims it now fits the resource budget.
