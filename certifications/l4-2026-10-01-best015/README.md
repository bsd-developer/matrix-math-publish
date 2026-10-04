# best015 verification package

The certified bound is

`omega_Q <= 43740440563687076465 / 18446744073709551616`

(approximately `2.3711740342311307`). Here `omega_Q` is the rational-field
matrix multiplication exponent defined in
`verification-source/lean/MatrixMath/Spec/OmegaExponent.lean`.

The canonical certificate is **458,921,565 bytes**, SHA-256
`dfcede72c9dbf8eaf7b55f34cdd56d93dca7fe8a28fca2787466bec410f1873f`.
The generated theorem is supplied as a losslessly compressed payload; its raw
identity is recorded in `manifest.json`.

Read `trust-boundary.md` and follow `verification-runbook.md` to build the
checkers and verify the certificate. Run `python3 verify-files.py` here to check
file identity; that command does not establish mathematical acceptance.

The supplied CN assurance records identify the theorem, its exact statement,
and its axiom dependencies. Their original full-source closure digest is not
the digest of this reduced verification workspace. Building the supplied source
does not itself establish acceptance of the full certificate; the runbook
provides separate commands for exact verification and full Lean certification.

`verification-source/` contains the Rust checker/CLI, 22 unchanged Lean proof
and checker modules, and their build support. Cargo.lock matches this workspace
and retains the original versions and checksums of every included dependency.
The CLI's generic `mm-search` dependency is included because it is required to
build; optimizer code, campaign data, private telemetry, and Git history are
not included.

The large certificate and compressed theorem belong in `payloads/`, which is
excluded from ordinary Git commits. The manifest lists the small package files
and the two separate payloads.
