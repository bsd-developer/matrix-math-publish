# ADR 0011 — Outward dyadic rounding of directed enclosures

- Status: **accepted** — the amendment is `docs/specs/0011_spec.md`, the Lean
  mirror is the `floorDyadic`/`ceilDyadic` snap in
  `lean/MatrixMath/Numeric/Log2Bounds.lean`, and the `dyadic-rounding` feature
  is deleted in favour of unconditional rounding
- Spec version: 2.1.0
- Supersedes: none

## Post-acceptance measurements (2026-08-23)

The legality decision was forced by the general-`ℓ*=4` cost-model measurement
(`docs/notes/2026-08-23/cost-model-l4.md`): the unrounded producer
precision-derivation pass on the 414.9 MB general `ℓ*=4` certificate was
killed unfinished at 80 CPU-minutes, profile pinned on malachite mul/GCD —
this ADR's coprime-denominator pathology — while the rounded build finished
the same input in 5,653 s under heavier co-tenancy, with
`log_evaluations = 25,763,780` (310× the `ℓ*=3` general count).

## Context

`docs/experiments/omega-l4.md` records that exact evaluation does not scale to
`ℓ*=4`: `mm omega-min` held a core for 9 h 19 m without returning, against a
4.2 h estimate obtained by scaling the measured `ℓ*=3` cost linearly in block
count. That document names the behaviour "superlinear in block count" and
`0007_spec.md` was rewritten around the diagnosis.

**The diagnosis was wrong, and the block count is not the variable.** The cost is
`Θ(n^2.7)` in the *length of every distribution summed*.

The mechanism is visible in the artifacts. `lower(E_total)` at `ℓ*=3` is a
rational with **3,647,463 digits**. A directed entropy bound is
`Σ -pᵢ·log2ᵣ(pᵢ)`, and each term's denominator is `den(zᵢ)^(2N-1)·lcm(odd)` with
a *different* `zᵢ` per term. Those factors are pairwise coprime, so an
accumulator's bit length grows linearly in the number of terms and the cost of
summing them grows quadratically or worse. Measured on terms built exactly as
`log2.rs` builds them:

| terms | sequential | pairwise | rounded to `2⁻⁹⁶` first | result size |
|---:|---:|---:|---:|---:|
| 81 | 286 ms | 115 ms | **0.4 ms** | 290,728 → **99 bits** |
| 256 | 6,755 ms | 1,146 ms | **1.4 ms** | 1,282,865 → **99 bits** |
| 729 | 99,480 ms | 29,521 ms | **5.7 ms** | 6,271,221 → **99 bits** |

`ℓ*=4`'s root mixtures live on 6,561-entry supports where `ℓ*=3`'s live on 81,
which is why the level that was merely slow becomes a level that does not finish.

## Decision

Round every directed enclosure **outward** onto a shared grid `2⁻ᴮ` as it is
produced — `floor_dyadic` for a lower bound, `ceil_dyadic` for an upper bound —
with

```text
B = log_precision_bits + 32.
```

Rounding at the point where an enclosure is *produced* is sufficient and is
where `precision` is in scope. It is not necessary to round every propagation
step — but the reason rests on a premise this ADR must state, because it is
load-bearing and nothing in `mm-rat` enforces it.

The next operation after a rounded `log2` enclosure is `scale(-p)` in
`term_enclosure_with`, which multiplies both endpoints by the probability `p`.
That would leave denominator `2ᴮ · den(p)` and destroy the shared grid in one
step — **except that every certificate rational is dyadic**: §7.5 step 4 rounds
every emitted probability to a `rational_bits`-wide dyadic
(`python/mm_opt/rationalize.py`). So `den(p)` is a power of two, the product
stays on a power-of-two grid, and additions remain shift-and-adds. The one place
the dyadics are left — the division by `mass` in `weighted_conditional_entropy`
— divides a whole distribution by a single value, so the lcm stays bounded.

**A future change that admits a non-dyadic certificate rational silently voids
this argument and the measured speedup with it.** If that becomes possible, the
rounding must move into `term_enclosure_with` *after* the scale, where the grid
claim holds unconditionally.

## Soundness

One line per direction, and it composes through every §7.2 rule:

- `floor(x) ≤ x`, so a rounded lower bound is still a lower bound.
- `ceil(x) ≥ x`, so a rounded upper bound is still an upper bound.

Every rounding therefore moves the A21 verdict **toward rejection**: `E_total`
and `M_total` shrink, the requirement grows, `h_max` grows so `term1` shrinks.
**Rounding cannot accept a certificate the unrounded checker rejects.** That is
the entire soundness delta, and it is what makes the Lean obligation small.

`Interval::new`'s invariant survives, since `floor(lo) ≤ lo ≤ hi ≤ ceil(hi)`.

## Why `B = precision + 32` and not less

The composed width of one evaluation is currently about `0.7 · 2⁻ᵖ`; **one**
rounding per evaluation adds under `2⁻⁽ᵖ⁺³²⁾`, so the total stays under `2⁻ᵖ` and
`0004_spec.md` P1's `tol(precision) = 2⁻ᵖ` continues to hold **unamended**.

(An earlier draft of this section said "three roundings", transplanting the
three-way spare-bit budget of `0002_spec.md` L2. `round_outward` has one call
site. The conclusion is unaffected — one is fewer than three, so the bound was
conservative — but this paragraph is what someone writing the §7.2 amendment and
the Lean mirror will read to learn what to mirror, and it must say what the code
does.)

| `B` | accumulated error at `ℓ*=4` | `ΔΩ` | against the `2⁻⁶⁴` grid `Ω` is reported on |
|---:|---:|---:|---|
| 80 | 1.33e-18 bits | 4.4e-19 | ~8 ulps — could move `Ω` |
| **96** | **2.03e-23 bits** | **6.7e-24** | four orders below → `Ω` bit-identical |
| 128 | 4.7e-33 bits | 1.6e-33 | free, and overkill |

So `0004` is untouched: P1, P4, and P5 all continue to hold as written, and
`log_evaluations` is unchanged because a rounding is not an evaluation.

## Measured

Implemented behind the `mm-rat/dyadic-rounding` feature so the two arms are the
same source built two ways.

| | control | rounding | |
|---|---:|---:|---:|
| symmetric `ℓ*=3` wall clock | 72.3 s | **15.5 s** | **4.66×** |
| `omega_min` | 2.372156220666089 | identical | |
| `omega_ceiling` | `43758558705485441543/2⁶⁴` | **bit-identical** | |
| `log_evaluations` | 14,534 | identical | |

The certified `Ω` ceiling is bit-identical on all three committed fixtures —
`omega-l2-hand`, `omega-l3-optimized`, and `omega-l3-uniform`. The predicted
`ΔΩ` of `6.7 × 10⁻²⁴` against a `2⁻⁶⁴ ≈ 5.4 × 10⁻²⁰` reporting grid says it
should be, and it is.

Reproduce with:

```sh
cargo build --release -p mm-cli --features mm-rat/dyadic-rounding
just test-rounding
```

**§5.7 is verified, not assumed.** It requires both evaluators to round
identically, and `crates/mm-exact/tests/symmetric_masses.rs` asserts *exact
rational equality* of all six A20 bounds between the general and symmetric
paths. Under the feature, all six of its tests pass in 219.8 s — including
`the_symmetric_path_reproduces_every_bound_without_expanding` at `ℓ*=2`,
`ℓ*=3`-optimized and `ℓ*=3`-uniform. That is the only configuration in which a
§5.7 violation was possible, and until `just test-rounding` existed no tier
built it.

At `ℓ*=4`, produced and checked:

| | |
|---|---:|
| Producer | 376.2 s |
| Checking | 183.8 s |
| Certified `Ω` | 2.372698028664 |
| Evaluations | 1,018,052 |

against a previously recorded 9 h 19 m that never returned.

## Consequences

- **`0007_spec.md` §5.7 forbids one evaluator performing a rounding step the
  other does not.** So this is compile-time and workspace-wide, never a runtime
  switch: a binary rounds in both evaluators or in neither, and a certificate's
  verdict becomes a property of the binary that decided it.
- **`0001_spec.md` §7.2 fixes the directed propagation rules normatively**, so
  making this the default requires an amendment there, and the Lean checker must
  mirror it or the two implementations decide different things. Neither is
  written. **Until both are, no certificate produced under this feature may be
  published**, and the feature stays off by default.
- `MaxEntropyBlock::certify` step 4 becomes marginally stricter: endpoints move
  outward by `≤ 2⁻⁹⁶` against an `ε` of `4.4 × 10⁻¹⁰`, ten orders of margin. No
  committed block fails, but the corpus must be re-verified when this lands.
- `docs/experiments/omega-l4.md`'s "superlinear in block count" should be
  corrected to name the distribution length. `0007_spec.md`'s value does not
  change — it still removes the redundancy that makes `ℓ*=4` addressable — but
  the stated reason is wrong, and a wrong reason recorded as a finding is how
  the next decision gets made badly.

## Rejected alternatives

**Pairwise summation alone** (already landed, `0002`). Measured 2.5–5.9×, and it
is subsumed: once accumulators are 99 bits, bracketing stops mattering. It was
worth landing because it is unconditional and needs no amendment, but it does
not make `ℓ*=4` finish.

**A different bignum library** (`rug`/GMP). Typically 2–5× on operations at these
sizes, but it breaks `mm-rat`'s `no_std`, adds a C dependency and an LGPL
constraint, and enlarges the trusted computing base. It is also moot: at 99 bits
the bignum library stops mattering.

**Raising the precision instead.** Backwards — `docs/experiments/omega-l3.md`
records that 64 and 256 bits give a bit-identical certified `Ω`, so precision is
not what is limiting the bound.
