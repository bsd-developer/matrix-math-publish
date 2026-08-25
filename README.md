# A machine-checked bound on the matrix multiplication exponent

This repository contains a fully machine-checked proof that

```
ω ≤ 10935605172023554189 / 2^62 = 2.371281376990…
```

where ω is the matrix multiplication exponent. The entire argument is a
certificate: an exact rational witness (`artifacts/`) whose validity is
verified independently by an exact Rust checker (`crates/`) and closed as
a Lean 4 theorem (`lean/`). No floating-point computation is trusted
anywhere in the claim.

| Bound (ω ≤) | Year | Team | Machine-checked |
|---|---|---|---|
| 2.371339 | 2025 | Alman et al. | no |
| **2.371281377** | **2026** | **this work** | **yes** |
| 2.371177 | 2026 | Dupont et al. (Google DeepMind) | no |

The bound improves the best published level-three result and, to our
knowledge, is the first bound on ω in this range whose statement and
verification are closed inside a proof assistant. The stronger 2.371177
is a level-four floating-point claim without machine-checked
verification; we make no claim against it.

Pre-Print: https://zenodo.org/records/22101463

## Runbook

Prerequisites: [rustup](https://rustup.rs) (the pinned toolchain in
`rust-toolchain.toml` is picked up automatically),
[elan](https://github.com/leanprover/elan) (Lean 4, pinned by
`lean/lean-toolchain`), [just](https://github.com/casey/just), and
Python 3.12.

```sh
just doctor
just build
just verify artifacts/omega-55148017.certificate.json
just prove  artifacts/omega-55148017.certificate.json
```

- `doctor` checks the pinned toolchain versions.
- `build` compiles the Rust checker and the Lean development.
- `verify` runs the independent exact Rust verification of the
  certificate; it reports the certificate digest
  (`55148017090a8883ab18bbd1316196fadc32b2f5f41cbf751d838d5c334f895f`)
  and the certified value.
- `prove` generates and checks the certificate-specific Lean theorem
  under profile CN and prints the axiom report.

The specification the checkers implement is in `docs/specs/`; the
rounding and definitional-ω decisions are recorded in `docs/adr/`. The
accompanying paper is in `paper/`.
