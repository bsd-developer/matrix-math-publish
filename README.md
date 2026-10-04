# Certified matrix multiplication bounds

This repository provides certificate bytes, independent verification source and
papers under the publishing identity **bsd-developer** (BSD), contact
**bsd.developer@proton.me**. The latest prepared result is search043:

**ω_Q ≤ 43740354192942056903 / 18446744073709551616 ≈ 2.371169352063661.**

Here `ω_Q` is the rational-field matrix multiplication exponent defined in
[`OmegaExponent.lean`](certifications/l4-2026-10-04-search043/verification-source/lean/MatrixMath/Spec/OmegaExponent.lean).
The exact rational is the claim; the displayed decimal is approximate.

| Result | Exact certified upper bound on ω_Q | Approximate decimal | Reader package |
|---|---|---:|---|
| search043 | `43740354192942056903 / 18446744073709551616` | **2.371169352063661** | [Package](certifications/l4-2026-10-04-search043/README.md), [paper PDF](certifications/l4-2026-10-04-search043/paper/build/paper.pdf) |
| best015 | `43740440563687076465 / 18446744073709551616` | 2.371174034231131 | [Historical package](certifications/l4-2026-10-01-best015/README.md), [paper PDF](certifications/l4-2026-10-01-best015/paper/build/search-methods.pdf) |
| Earlier level-four result | `43740492065107743983 / 18446744073709551616` | 2.371176826128739 | [Historical source](certifications/l4-2026-09-30/README.md) |

These are locally certified results under **CN**, with the trust assumptions
below. The search043 GitHub release is currently a **draft**; final downloaded
reader-path verification and publication are pending. Historical payloads are
not supplied by the search043 release; each result must be checked against its
own certificate and matching source.

## Trust boundary

CN uses `Classical.choice`, `propext`, `Quot.sound`, one certificate-specific
native-evaluation axiom, and `MatrixMath.AX1_combination_loss`. AX1 represents
the cited combination-loss feasibility theorem, whose proof is not formalized
in these packages. The relevant Lean compiler, native runtime and GMP are
trusted; kernel soundness is a metatheoretic assumption. These are neither
kernel-only nor axiom-free proofs. See the result's
[trust boundary](certifications/l4-2026-10-04-search043/trust-boundary.md) and
[compiled assurance](certifications/l4-2026-10-04-search043/compiled-assurance.json).

## Verify search043

Follow the [verification runbook](certifications/l4-2026-10-04-search043/verification-runbook.md).
The 459,013,469-byte canonical certificate and compressed Lean theorem are
separate release assets, excluded from Git's source archives. Download them
alongside the verification archive and its checksum file when the release is
available. File hashing establishes identity; Rust checking and full Lean CN
execution establish fresh acceptance under the disclosed assumptions.

External trust anchors:

- Certificate: **459,013,469 bytes**, SHA-256
  `1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521`.
- Decompressed generated Lean module: **459,016,569 bytes**, SHA-256
  `7a2b439bed7c9caf3e3e59a0ee338b84c21efa51acacda2419448465d83f2786`.

The original frozen source completed independent exact Rust checks, two whole
CN executions, compiled statement/axiom audits, trust-base closure and four
byte-identical replay comparisons. Fresh full execution from the reduced
release package with newly downloaded dependencies has **not** been tested.

## Papers and citation

The [paper index](papers/README.md) links each paper to its result. Papers share
the bibliography and build support in `papers/shared/` and `papers/build.sh`.
See [CITATION.cff](CITATION.cff) and [LICENSE](LICENSE). A search043 Zenodo version
DOI has not yet been assigned; no DOI for another publishing identity is used.

See [result versions](RELEASES.md) for release and DOI status.
