# 2.37116935 verification package

The certified upper bound is

`omega_Q <= 43740354192942056903/18446744073709551616`

(approximately `2.371169352063661`). Here `omega_Q` is the rational-field
matrix multiplication exponent defined in
`verification-source/lean/MatrixMath/Spec/OmegaExponent.lean`.
The exact rational is the claim; the displayed decimal is an approximation.

The canonical certificate is **459,013,469 bytes**, SHA-256
`1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521`.
The generated theorem is supplied losslessly compressed in `payloads/`.
Its decompressed identity is **459,016,569 bytes**, SHA-256
`7a2b439bed7c9caf3e3e59a0ee338b84c21efa51acacda2419448465d83f2786`.
See the [paper PDF](paper/build/paper.pdf), [source](paper/paper.md) and aggregate
[data inventory](paper/data/manifest.json).

Read `trust-boundary.md` and follow `verification-runbook.md` to build the
checkers and independently verify the certificate. Run `python3 verify-files.py`
here to check file identity; that command does not establish mathematical
acceptance. The recorded local certification completed two full CN executions,
independent exact Rust checks, compiled statement/axiom audits and a same-source
local replay. The four deterministic result artifacts matched byte-for-byte.
A clean-room run of the runbook from freshly downloaded release assets passed on
2026-10-04, including full CN certification.

The supplied CN assurance records identify the exact theorem statements and
their axiom dependencies. They use the published combination-loss theorem as
`MatrixMath.AX1_combination_loss`; that theorem is not formalized in this package.
CN also uses certificate-specific native evaluation and trusts the relevant
Lean compiler, runtime and GMP. This is not a kernel-only or axiom-free proof.

`verification-source/` contains the unchanged Rust checker/CLI and 22 Lean proof
and checker modules, with pinned dependencies and minimal build support.
Cargo.lock matches this reduced workspace and retains the original versions
and checksums. The CLI's generic `mm-search` library is included because it is a
build dependency. The private optimizer, search campaign, telemetry and Git
history are not included.

The recorded original full-source closure digest differs from the digest of
this reduced verification workspace. Building this source does not itself
establish acceptance of the complete certificate; the runbook separates builds,
exact Rust checking and full Lean certification.

The two large payloads are excluded from ordinary Git commits. The manifest
lists them separately from the small source and assurance files. The release source archive contains these small files; the certificate and
compressed theorem are separate assets of the same
[GitHub release](https://github.com/bsd-developer/matrix-math-publish/releases/tag/l4-2026-10-04-search043).

The verification archive includes this package, the shared paper build support,
repository licence texts and citation file. Its root contains `certifications/`
and `papers/`, matching the tagged repository layout.
