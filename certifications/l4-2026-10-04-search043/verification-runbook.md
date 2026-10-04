# Verify 2.37116935

Start in this certification directory with both files present in `payloads/`:
`certificate.json` and `Omega_1a05ebc4e32c1a21.lean.gz`.

## Obtain the release files

Download `l4-2026-10-04-search043-verification.tar.gz`, `certificate.json`, and
`Omega_1a05ebc4e32c1a21.lean.gz` from the
[release page](https://github.com/bsd-developer/matrix-math-publish/releases/tag/l4-2026-10-04-search043).
The automatic GitHub source archives do not include the two payloads.
`release-assets-SHA256SUMS.txt` provides checksums for these downloads.

In a directory containing the three downloaded files:

```sh
tar -xzf l4-2026-10-04-search043-verification.tar.gz
mkdir -p l4-2026-10-04-search043/payloads
mv certificate.json Omega_1a05ebc4e32c1a21.lean.gz l4-2026-10-04-search043/payloads/
cd l4-2026-10-04-search043
```

The steps below independently verify the package and its mathematical result
under the disclosed CN/AX1 trust boundary.

## Trust anchors

`verify-files.py` checks files against `manifest.json`, which ships in the same
package. The external anchors are the digests printed in the paper (§4 and
Appendix A) and the release tag `l4-2026-10-04-search043`:

- certificate: 459,013,469 bytes, SHA-256
  `1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521`;
- generated module: 459,016,569 bytes, SHA-256
  `7a2b439bed7c9caf3e3e59a0ee338b84c21efa51acacda2419448465d83f2786`.

## Hardware and expected durations

The recorded runs used an Apple M1 Max laptop with 64 GiB unified memory, on CPU
only.

| Run | Peak whole-system memory in use | Command elapsed |
|---|---|---|
| First full CN | about 34 GiB | 13,908 s (3.9 h) |
| Whole-module CN replay | about 37 GiB | 14,985 s (4.2 h) |
| Exact Rust check | about 30 GiB | 793–827 s (13–14 min) |

The memory figures include roughly 20 GiB already in use by other processes when
each run started. Most work hovered around 35 GiB, so about 48 GiB of RAM is
expected to be a feasible upper limit. Machines with less memory are untested.

Allow disk space for:

- the 459 MB certificate;
- the 459 MB generated module;
- Lean build outputs;
- the Mathlib cache.

## Check file identities

```sh
python3 verify-files.py
```

This checks file hashes and the compressed theorem's decompressed hash and byte
count. It checks identity, not mathematical acceptance. The certificate must
have SHA-256
`1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521`
and contain 459,013,469 bytes.

## Prepare an isolated workspace

Prerequisites: Python 3.12 or later, Git, a C toolchain, Rustup with Rust 1.94.0,
and Elan with Lean 4.33.0. Toolchains are selected by the supplied
`rust-toolchain.toml` and `lean-toolchain`. Dependency versions are fixed by
`Cargo.lock` and `lake-manifest.json`. Do not regenerate the locks or run
`lake update` to work around a verification failure.

Building and proving write outputs, so use a disposable copy:

```sh
READER_WORKSPACE="$(mktemp -d)"
cp -R verification-source "$READER_WORKSPACE/verification-source"
cp -R payloads "$READER_WORKSPACE/payloads"
cd "$READER_WORKSPACE/verification-source"
export CARGO_BUILD_JOBS=1
export LEAN_NUM_THREADS=1
```

Initial dependency acquisition needs the public Cargo registries, Git
repositories, and Mathlib cache. Caches of the exact pinned dependencies may be
reused; this does not require reusing project build outputs.

## Build the Rust checker

```sh
cargo build --release --locked -p mm-cli --bin mm
target/release/mm --version
```

With the pinned crates cached, add `--offline` to build without network access.

## Build the Lean checker and soundness proofs

```sh
cd lean
lake exe cache get
lake --no-cache build MatrixMath
lake env lean --version
cd ..
```

The cache command prepares the pinned external dependencies. The project build
compiles the supplied checker, general soundness proofs, and result-assurance
code. It does not evaluate the 2.37116935 certificate.

## Run the independent exact Rust check

```sh
target/release/mm verify ../payloads/certificate.json --skip-lean --json
```

Require a successful exit. The recorded run printed exactly this JSON:

```json
{"canonical_sha256":"1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521","certification":"XC","claim":"omega <= 43740354192942056903/18446744073709551616","kind":"omega","note":"no Lean theorem was built, so this is a development cross-check and is not reportable as certified (§3.4)","rust_cross_check":"ok","schema":"matrix-math-certificate/1","verdict":"VERIFIED"}
```

`"certification":"XC"` is expected: this step is an exact cross-check, not the
Lean theorem. Rust agreement does not replace the Lean theorem. Rust and Lean
implement the same specification transcription, so their agreement does not
detect a shared transcription error (see "Audit the AX1 bridge" below).

## Run full Lean certification

```sh
target/release/mm prove ../payloads/certificate.json --profile cn --json
```

This expensive command runs the Rust prerequisite, regenerates the module from
the complete certificate, builds its proof dependencies, evaluates the full
certificate, and audits the compiled theorem statements and axioms. It writes
assurance under `docs/results/<certificate-sha256>/`. Require a successful
process exit and compiled audit; output files alone do not establish success.

Compare the regenerated module's raw SHA-256 with `generated_module` in
`manifest.json`. Compare the emitted compiled assurance with
`compiled-assurance.json`: declaration kinds, elaborated statements, statement
digests, and transitive axioms must agree. Review the new execution's TCB.
Record its reduced source-closure digest separately from the original
full-source digest in the supplied assurance records.

The expected profile is CN: the result depends on the three standard Lean
axioms, `MatrixMath.AX1_combination_loss`, and one certificate-specific native
axiom. See `trust-boundary.md`. The compressed theorem is available for source
inspection and literal comparison; it is not a substitute for the full
certificate computation.

## Audit the AX1 bridge

The result is only as trustworthy as the Lean transcription of the cited
combination-loss problem (Eq. (11) of Dupont et al., arXiv:2608.16884). AX1
asserts that feasibility of that problem implies the exponent bound. If the
transcription were not faithful, AX1 could be false.

To audit it:

1. Compare `verification-source/lean/MatrixMath/Spec/Instance.lean`
   (`CombinationLossFeasible` and the A.1–A.10 definitions) with Eq. (11) and
   Appendix A of `verification-source/docs/specs/0001_spec.md`.
2. Use `verification-source/docs/traceability.md`, which maps each spec
   equation to its Lean declaration and Rust implementation.

The traceability table is a literal copy of the generated project file. Its
Python column and some Rust paths refer to the full project source, which is not
included in this reduced package. Its Lean declarations are in
`verification-source/lean/`.

