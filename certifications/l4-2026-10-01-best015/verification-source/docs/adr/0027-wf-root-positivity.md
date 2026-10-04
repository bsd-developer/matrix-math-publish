# ADR 0027 — Derive root and interior positivity checks from WF

Status: accepted design; public compilation and integration checks are required
before claiming the optimization is validated. Spec version: 2.1.0.

## Context

Experiment 0095 measured the original first root block at 0.182 seconds and its
306 directed logarithm endpoints at 0.125 seconds. These limited observations
make redundant beta/eta construction in root acceptance a plausible next target;
they do not establish the runtime of all six blocks or the final lower bound.

Experiment 0096 proved entrywise nonnegativity of recursive beta distributions
from `ANode.WF`. Nonnegative root weights and mixtures then imply the non-block
root side conditions. Its complete-check function equality retains the WF
prefix, so it also covers malformed instances. All four targets passed private
compilation and axiom checking with only `propext`, `Classical.choice`, and
`Quot.sound`. Both proof stages and their cumulative resource charges are retained.

## Decision

Keep `TrackACert.check` as the unchanged reference definition. Promote the exact
successful proof statements, bodies and replacement definitions to
[`WFRootPositivity.lean`](../../lean/MatrixMath/Certificate/WFRootPositivity.lean).
Only documentation identifying the private draft is updated. The original
integration registered `check_eq_checkRootBlocks` as `@[csimp]`, following
ADR 0015's proved compiler-substitution approach. The interior extension below
replaces that attribute with one direct equality from the original checker;
the root equality remains a proof intermediate.

[`Schema/Omega.lean`](../../lean/MatrixMath/Schema/Omega.lean) imports the new
module before its byte-checker definitions compile. The dependency remains
acyclic: Schema imports the proof module, which imports the original OmegaCheck.
A late import through theorem inventory or result assurance would not substitute
calls in an already compiled Schema module.

The original root-only replacement retains the exact WF check, omega sign check, six original root
block domains and default blocks, all interior and leaf checks, and the final
exact rational inequality. WF does not make invalid blocks acceptable. Only the
root positivity checks already implied by WF are removed at that stage.
The interior extension below removes the corresponding proved interior tails.
Root value calculations, decoding, byte/claim/digest binding, certificate
formats, independent Rust checking, and the existing CN TCB remain unchanged.
No conditional regional theorem is registered as a compiler rewrite.

## Verification and limits

The four exact statements enter the compiled theorem inventory with no new
project axiom or residual mathematical assumption. The successful private proof
snapshot, the public prose/attribute diff, and public compiled assurance remain
separate evidence. A failed private stage is preserved, not reclassified.

[`CheckWFRootPositivity.lean`](../../lean/scripts/CheckWFRootPositivity.lean)
compares a separately named original complete-check body, the direct replacement
and a compiled public caller. Fifteen L2 cases exercise a valid fixture, WF-false
mutations, invalid beta/mu, missing or malformed blocks with valid WF, and a
negative omega. The reference must not call the public checker, which would turn
the comparison into a self-comparison after substitution. Existing byte-level
malformed, precision and resource-limit tests remain applicable.

Normal build, compiled axiom/statement assurance, the focused exact comparisons,
and inspection of actual emitted Schema call paths must pass before integration
is reported as validated. Existing claims and all other inventory entries remain.
The universal Boolean equality is the correctness argument; finite fixtures test
wiring and rejection behavior. Neither proves a full-level-four runtime saving.
A complete certificate-specific CN attempt requires separate registration and all
ordinary byte, claim, digest, Rust, Lean and assurance gates.

## Interior extension (0104/0106)

The qualified 0102 phase diagnostic finishes the reduced root gate in 1.131
seconds and times out inside level-three interior acceptance. It does not
identify the cost of individual regional subcomputations. Experiment 0104
proves that child WF implies all trailing regional positivity checks, then
transports WF through reached nodes and selected positive branches. The array
and interior equalities retain level selection, six regions, both arrays,
`offset + 6*j + r`, default entries/blocks and fallback behavior. The original
mass sign, defaulted allocation sign and block check remain in each region.

All eleven root/interior targets compile with only the standard three axioms.
The sole 58-case private fixture and independent actual-C review pass; the
initial failed simplification and its charge are retained. See the
[0104 report](../experiments/0104-wf-interior-positivity.md). Promote its exact
successful proof bodies under the separately registered
[0106 verification allocation](../specs/0106_spec.md), changing only the module
documentation. Register `check_eq_checkRootInteriorBlocks` directly as the sole
original-check `@[csimp]` equality. Neither regional conditional theorem is a
compiler rewrite. The existing WF prefix makes the complete equality
unconditional and preserves malformed-input rejection.

Add the seven new targets to compiled assurance while retaining all sixty prior
entries unchanged. Compare private/public compiled statements for all eleven
targets. The production interior fixture imports Schema and preserves the 45
regional, seven array and six malformed whole-check comparisons; the fifteen
existing L2 cases also compare the new direct replacement. Actual Schema C
must dispatch to that replacement on both decode-success paths. Public
integration verification remains pending until its receipts pass. The known
full-regression failure remains explicit. No level-four speedup or CN acceptance
follows from these proofs or small fixtures.

## Alternatives

Directly replacing the reference checker would change the definition unfolded by
existing soundness proofs and require unnecessary proof restructuring. Replacing
root checks unconditionally without the WF prefix would change malformed-input
behavior. Removing block checks or directed value evaluation is not justified by
this theorem. None of those changes is part of this decision.
