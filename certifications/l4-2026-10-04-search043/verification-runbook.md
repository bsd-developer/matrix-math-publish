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

Require a successful exit, the exact certificate hash, the rational claim
`43740354192942056903/18446744073709551616`, and
`rust_cross_check: ok`. Rust agreement does not replace the Lean theorem.

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
