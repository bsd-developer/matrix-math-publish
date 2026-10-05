# Trust boundary

This result uses the CN profile. It is not an axiom-free or kernel-only proof.

The supplied `compiled-assurance.json` records the compiled statements and
transitive dependencies. The exponent-bound theorem depends on:

- `Classical.choice`;
- `propext`;
- `Quot.sound`;
- `MatrixMath.AX1_combination_loss`; and
- one certificate-specific `native_decide` axiom, whose complete name and type
  are recorded in the audit.

The project proves the directed checker sound and establishes certificate
feasibility. AX1 supplies the cited mathematical theorem connecting those
feasibility conditions to the exponent bound; its proof is not formalized in
this package. AX1 is only as trustworthy as the Lean transcription of the
cited problem; `verification-source/docs/traceability.md` and the runbook's
"Audit the AX1 bridge" section describe how to check it. Rust and Lean implement
the same transcription, so their agreement does not detect a shared
transcription error.

CN also trusts the relevant pinned Lean compiler, native runtime, and
big-integer implementation. Lean kernel soundness is a metatheoretic assumption.
The independent exact Rust checker provides corroboration, but is not the
Lean theorem's authority. The generator and transport tools do not replace
checking the canonical certificate bytes.

`assurance.json` and `tcb.json` are the recorded result assurance and TCB.
A fresh run's `tcb.json` may misreport the Lean and Lake versions; see the
runbook's known-defect note.
`runtime-trust-summary.json` summarizes compiler/runtime/GMP and library
versions without private filesystem bindings. The recorded original
full-source closure is distinct from this reduced verification workspace.

`verify-files.py` checks the supplied file identities and lossless theorem
transport. Building the source checks compilation. Neither operation by itself
establishes fresh acceptance of the complete certificate. Follow the runbook's
separate full-verification steps to reproduce the mathematical result.
