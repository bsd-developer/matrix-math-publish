# Verify 2.37116935

A clean-room run of this runbook from freshly downloaded release assets passed
on 2026-10-04: identical Rust output, full CN certification, and a regenerated
module and compiled assurance byte-identical to the shipped ones.

## Obtain the release files

Download `l4-2026-10-04-search043-verification.tar.gz`, `certificate.json`, and
`Omega_1a05ebc4e32c1a21.lean.gz` from the
[release page](https://github.com/bsd-developer/matrix-math-publish/releases/tag/l4-2026-10-04-search043).
The automatic GitHub source archives do not include the two payloads.
Also download `release-assets-SHA256SUMS.txt`, whose own digest is in the
release notes.

In a directory containing the four downloaded files:

```sh
shasum -a 256 -c release-assets-SHA256SUMS.txt
tar -xzf l4-2026-10-04-search043-verification.tar.gz
mkdir -p l4-2026-10-04-search043/certifications/l4-2026-10-04-search043/payloads
mv certificate.json Omega_1a05ebc4e32c1a21.lean.gz l4-2026-10-04-search043/certifications/l4-2026-10-04-search043/payloads/
cd l4-2026-10-04-search043/certifications/l4-2026-10-04-search043
```

The extracted archive retains the tagged repository layout: this package is in
`certifications/l4-2026-10-04-search043/`, with shared paper build files in root
`papers/`. From the package directory, `bash paper/build.sh` builds the paper;
it is not necessary for certificate acceptance.

The steps below run from this package directory, with `certificate.json` and
`Omega_1a05ebc4e32c1a21.lean.gz` in `payloads/`. They independently verify the
package and its mathematical result under the disclosed CN/AX1 trust boundary.

## Trust anchors

`verify-files.py` checks files against `manifest.json`, which ships in the same
package. The external anchors are the digests printed in the paper (§2 and
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
| Clean-room CN, under concurrent load | 40.0 GiB | 16,209 s (4.5 h) |
| Exact Rust check | about 30 GiB | 793–856 s (13–14 min) |

The whole-system figures include other workloads (roughly 20 GiB when each run
started). In the clean-room run the `mm`/`lake`/`lean` process tree itself
peaked at 15.4 GiB. A machine with 48 GiB total RAM is expected to suffice;
machines with less memory are untested. Expect CN to take about 4–4.5 h.

The clean-room run used about 9.1 GiB of disk in the work directory, plus the
shared Mathlib cache in `~/.cache/mathlib`:

- Lean packages (`lean/.lake/packages`): 7.5 GiB;
- copies of the payloads: about 1.1 GB;
- the regenerated module: 0.46 GB;
- the Rust `target/` directory: 112 MB.

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
PACKAGE="$PWD"
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
code. It does not evaluate the 2.37116935 certificate. It ends with 0 errors;
8 linter warnings (unused tactics and variables) are expected.
`lake env lean --version` must report Lean 4.33.0, commit `d8b18978`.

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
certificate, and audits the compiled theorem statements and axioms. It prints
nothing until it finishes, typically after several hours; this is expected.
It writes the module to `lean/MatrixMath/Generated/Omega_1a05ebc4e32c1a21.lean`
and assurance to `docs/results/<certificate-sha256>/`. Require a successful
process exit and compiled audit; output files alone do not establish success.

Compare the outputs with the package:

```sh
CERT=1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521
MODULE=lean/MatrixMath/Generated/Omega_1a05ebc4e32c1a21.lean
shasum -a 256 "$MODULE"   # 7a2b439bed7c9caf3e3e59a0ee338b84c21efa51acacda2419448465d83f2786
wc -c < "$MODULE"         # 459016569
gunzip -c ../payloads/Omega_1a05ebc4e32c1a21.lean.gz | cmp - "$MODULE"
cmp "docs/results/$CERT/compiled-assurance.json" "$PACKAGE/compiled-assurance.json"
python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_source_closure"])' \
  "docs/results/$CERT/assurance.json"
```

The module hash must equal `generated_module` in `manifest.json`, and both
`cmp` commands must print nothing. A byte-identical compiled assurance means the
declaration kinds, elaborated statements, statement digests and transitive
axioms all agree. The new `assurance.json` should differ from the package's only
in `lean_source_closure`. For this reduced workspace that digest is
`101e0ae6b87074d8acee13c21446376a17b9657941b759752be9c1b1299b7029`, over its 22
`.lean` files. Record it separately from the original full-source digest in the
supplied `assurance.json`,
`0b7add6f623b0254565d2f18bfe9d29253b16c3467153c3d3de62073ecccef66`.

**Known defect in the new TCB ledger.** The new
`docs/results/<certificate-sha256>/tcb.json` may record the machine's default
Elan Lean and Lake versions instead of the pinned 4.33.0. The ledger runs
`lean --version` in `verification-source/`, which has no `lean-toolchain`, while
the proof runs in `lean/` with the pinned toolchain. Confirm the toolchain
actually used with `lake env lean --version` in `lean/`. The proof and compiled
assurance are unaffected. The packaged source is intentionally left unchanged,
so that it stays the exact source the clean-room run validated; the project
source will be corrected for later releases.

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

