# Historical level-four verification source

The original and optimized local implementations certified

`omega_Q <= 43740492065107743983 / 18446744073709551616`

approximately `2.371176826128739214…`, using the 458,886,875-byte certificate
with SHA-256
`f1b8a16f9f8a72e05c09f0275d3ea88387d5c3698fbfbded9ccb4432f21477aa`.

`verification-source/` preserves the formerly root-level Rust and Lean source
and its toolchain/dependency locks. The relocation changes paths, not source
bytes. This historical directory is not the search043 verification package;
its certificate and matching historical transport assets are not included in
the search043 release.

The historical profile is CN: standard Lean axioms, certificate-specific
native evaluation, `MatrixMath.AX1_combination_loss`, and the relevant
compiler/runtime/GMP trust base. Neither implementation is kernel-only or
axiom-free. Completed local checking is distinct from fresh remote reader
verification.

For the current independently checkable result, use
[search043](../l4-2026-10-04-search043/README.md) and its own certificate bytes.
See the [paper index](../../papers/README.md) for the historical papers.
