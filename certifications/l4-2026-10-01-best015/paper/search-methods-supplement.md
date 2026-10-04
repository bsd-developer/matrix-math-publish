---
title: "Supplementary Material: Search Procedure for the Tie-Manifold Case Study"
author: |
  BSD (bsd.developer@proton.me)\
  Independent Researcher
date: "Draft updated 2 October 2026"
---

# Search procedure and result boundary

This supplement accompanies *A Machine-Checked Level-Four Bound on the Matrix Multiplication
Exponent: A Tie-Manifold Search Case Study*. AI agents assisted under the author's direction (paper,
Appendix D). The procedure below is a retrospective synthesis, not the
verbatim initial prompt or a guarantee of reproducing the numerical
trajectory. The private optimizer and campaign records are not prerequisites
for checking the supplied certificate.

The earlier eight-hour campaign began at numerical score
$2.3711894606957515$ and ended at $2.371176825455252$. Subsequent
continuation selected **point H**, with numerical score
$2.371174031813689$. The certified result is instead

$$
\omega_{\mathbb Q}\le\frac{43740440563687076465}{2^{64}}
=2.37117403423113\ldots.
$$

The paper measures branch geometry at point H using its frozen source.
The earlier prediction-agreement example concerns an earlier campaign model step.

# Retrospective research procedure

1. **Establish a numerical baseline.** Use a pinned implementation and an
   independently validated physical checkpoint. Distinguish the current
   global incumbent from a restored point used only to construct a local
   model. Preserve the best physical point even when a better-balanced
   construction seed has a worse hard score.
2. **Diagnose branch geometry.** Measure branch values, forty contrasts,
   their Jacobian, fitted convex weights and the projected gradient at the
   actual model origin. Check numerical rank and positivity. Use the exact
   mixture/slack identity to distinguish surrogate gain from hard gain;
   conditional search lemmas do not prove floating-point observations.
3. **Construct a reduced tangent model.** Form coupled tangent directions
   and estimate curvature using first-gradient differences at two scales.
   Check scalar slopes, mixed symmetry and model positivity. The native
   double-backward path failed a proved zero-curvature diagnostic and was
   not used for these models. Keep retained metrics associated with their
   original construction points.
4. **Evaluate finite moves and corrections.** Test bounded fractions with
   and without balance restoration. Target zero contrasts only where the
   branch and convex-mixture conditions justify it. Respect every physical
   domain. Select using the original hard exponent, never model gain alone.
   Record predictions, realized gains, slack and correction effects.
5. **Compare matched alternatives.** Compare model widths or alternative
   methods from the same checkpoint under explicit finite-trial controls,
   including setup costs. Added directions can improve the score while
   failing to justify their computation cost. Short unsuccessful controls
   do not establish general optimizer inferiority.
6. **Validate each promotion.** Require production, independently
   implemented reference and serialized/reloaded readouts. The recorded
   configuration was native400/reference1600/native400. Independently
   reconstruct the move and score components. A numerical crossing is not
   an exact bound or a convergence certificate.
7. **Certify the selected endpoint separately.** Freeze the rationalized
   witness, construct maximum-entropy witnesses and directed enclosures,
   and check the complete canonical bytes. Require independent exact Rust
   agreement, full Lean evaluation and compiled statement/axiom auditing.
   Distinguish the numerical score, exact claim and every remaining trust
   assumption. Search diagnostics are not premises of the bound theorem.

# What the reader can verify

The verification package `certifications/l4-2026-10-01-best015`
contains the matching checker sources, dependency locks, assurance and trust
records. Its `verification-runbook.md`
separates file-identity checking, source compilation, independent exact Rust
checking and full Lean CN certification. The canonical certificate is
458,921,565 bytes with SHA-256

```text
dfcede72c9dbf8eaf7b55f34cdd56d93dca7fe8a28fca2787466bec410f1873f
```

The current result depends on `Classical.choice`, `propext`, `Quot.sound`,
one certificate-specific native-evaluation axiom, and
`MatrixMath.AX1_combination_loss`, together with the relevant compiler,
runtime and GMP trust. Removing native evaluation and proving the full
combination-loss bridge are ongoing work, not completed results.

Two full local CN executions and their audits passed. Local retrieval and
byte comparisons do not establish completion of the separate remote
release-verification protocol. The certificate establishes one endpoint
under the disclosed assumptions; it does not prove global optimality,
search reproducibility or a comparative speed advantage.
