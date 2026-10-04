---
title: "A CN-Certified Level-Four Matrix Multiplication Bound: Adaptive Tangent Search on a Laptop"
author: |
  BSD (bsd.developer@proton.me)\
  Independent Researcher
date: "4 October 2026"
abstract: |
  We give an exact certificate for the rational-field matrix multiplication
  exponent bound $\omega_{\mathbb Q}\le 43740354192942056903/2^{64}
  =2.371169352063661\ldots$, below the displayed bound $2.371177$ of
  Dupont et al. The certificate is checked under the CN (native-certified)
  profile: a general Lean soundness proof plus one certificate-specific
  native-evaluation axiom. Numerical refinement and certification ran locally
  on an Apple M1 Max laptop, using CPU computation. The search builds small
  second-order tangent models and restores weighted branch balance before
  ranking candidates by the original nonsmooth objective. In eight recorded
  same-origin width comparisons the wider, nested model always scored lower,
  as its construction makes likely; only four met the recorded marginal
  compute-efficiency threshold. Earlier matched controls in the same campaign
  favored plain Adam. This is descriptive evidence from one adaptive
  campaign, not a claim of optimizer superiority. An independent exact Rust
  checker, a full Lean CN evaluation and a whole-module CN replay accepted the
  selected 459 MB certificate; compiled statements, axiom dependencies and
  deterministic replay artifacts were checked. The exponent inference uses the
  combination-loss feasibility theorem of Alman et al., as stated by Dupont et
  al., represented by an unproved Lean axiom in this package. Native evaluation
  and its compiler/runtime dependencies remain explicit. The certificate can be
  checked independently of the private numerical optimizer.
---

# 1. Result and scope

Every recent improvement to $\omega$ uses the laser method; the current
refinement is combination-loss analysis [@duan2023; @williams2024; @alman2025],
building on earlier laser-method bounds [@coppersmith1990; @legall2014; @alman2021].
Alman et al. formulated the finite optimization problem at the core of this
approach, showed that any feasible solution yields an upper bound on
$\omega$, and solved it at recursion level $\ell^*=3$ with sequential quadratic
programming [@alman2025; @gill2002]. Dupont et al. restated the problem
(their Eq. (11)) and its feasibility theorem (their Theorem 1, attributed to
Alman et al.), solved it at $\ell^*=4$ with a gradient method and AlphaEvolve,
and reported $\omega<2.371177$ [@dupont2026]. We use that level-four
formulation with Coppersmith--Winograd parameter $q=5$ and $\ell^*=4$. The
contribution here is a further numerical refinement with an exact,
independently checkable certificate and an explicit formal trust boundary.

Alman et al. computed at $\ell^*=3$; the level-four instance relies on the
feasibility theorem as stated for general $\ell^*$ in Dupont et al.'s Theorem 1.
We have not independently re-derived that theorem or the equivalence of the
level-four reformulation. Both are inherited through the axiom described in §5.

Let $\omega_{\mathbb Q}$ denote the rational-field matrix multiplication
exponent defined in the supplied Lean source. The result is

$$
\omega_{\mathbb Q}\le\Omega_*:=
\frac{43740354192942056903}{18446744073709551616}
=2.3711693520636610535\ldots.
\tag{1}
$$

Equation (1) is the Lean theorem's conclusion under the CN and
combination-loss assumptions specified in §5. It is not an axiom-free
derivation of the exponent bound. The exact rational is authoritative;
the displayed decimals are approximations. We make no all-fields claim.

The certified value is approximately $7.64794\times10^{-6}$ below Dupont et
al.'s displayed $2.371177$. That comparison uses their displayed upper bound.
Their unrounded value and their verification code had not been released when
this paper was written, so no claim is made about their unpublished checkpoint.

| Quantity | Value |
|---|---:|
| Numerical search score | **2.3711693500058737** |
| Exact certified bound, approximately | **2.3711693520636611** |

: Table 1. The selected point's numerical score and its distinct
outward-certified claim (1).

The certified claim exceeds the numerical score by approximately
$2.05779\times10^{-9}$. This difference includes rationalization and
outward certification bounds. It is not a floating-point error estimate.

This paper covers the whole level-four search campaign. That campaign had an
earlier exploratory phase, which ended at the numerical milestone
$2.371174031813689$, followed by the continuation reported in §3. Only the
final search043 endpoint is certified here. Earlier milestones are numerical
observations of the same campaign, not separate results.

# 2. Objective and local search model

## 2.1 Feasibility and the hard score

A physical point $p$ consists of distributions and leaf parameters on a
recursion tree. Different paths retain different parameters even when
their shapes coincide. Raw coordinates $\theta$ map to $p=\Phi(\theta)$
through softmax and interval parameterizations, following Dupont et al.
(their §3.1). Maximum-entropy subproblems are solved by Sinkhorn scaling
[@sinkhorn1967; @cuturi2013], as there. The search is approximate; the
certificate checks the resulting physical data exactly.

Write $E$ for the retained exponent contribution and $M$ for the matrix-size
exponent. At target $\tau$, the feasibility surplus is

$$
F_\tau(\theta)=E(\theta)+\tau M(\theta)-C,
\qquad C=8\log_2 7.
\tag{2}
$$

When $M>0$, $F_\tau\ge0$ is equivalent to $(C-E)/M\le\tau$. This is the
standard parametric (Dinkelbach) treatment of a ratio objective [@dinkelbach1967].
When $M(\theta)>0$, the numerical objective is

$$
\Omega_{\mathrm{hard}}(\theta)=
\max\left\{0,\frac{C-E(\theta)}{M(\theta)}\right\}.
\tag{3}
$$

The construction has twenty three-way minima over branches $X,Y,Z$:
six root sites, twelve interior sites, one level-two retained-exponent
site and one matrix-size site. Thus

$$
F_\tau=g_0+\sum_{i=1}^{20}a_i\min_k v_{i,k},\qquad a_i\ge0.
\tag{4}
$$

The coefficients include root weights, which are themselves optimized, and,
at the matrix-size site, the target $\tau$. Branch equality and weighted branch
balance therefore measure different things.

## 2.2 Tangent models and finite restoration

At a model origin $\theta_0$, choose one minimum-attaining reference branch
at each site. The other two branches give forty normalized contrasts

$$
c_{i,k}(\theta)=
\frac{a_i(\theta)\bigl(v_{i,k}(\theta)-v_{i,k_i^*}(\theta)\bigr)}{M_0},
\qquad k\ne k_i^*,
\tag{5}
$$

with Jacobian $J=Dc(\theta_0)$. Here $M_0=6.051764847062773$ is a fixed
normalization constant recorded with the search protocol, close to but not
equal to $M(\theta_0)$ (for example, $M=6.0530$ at the final origin).
Rank-checked solves with $JJ^\top$ project directions into the approximate
tangent space $\ker J$. This is a local numerical construction; it does not
prove that a global smooth tie manifold exists throughout the search.

The branch weights are fitted at the origin as the least-squares multipliers

$$
\lambda=\arg\min_\lambda\|\nabla f_{\mathrm{ref}}-J^\top\lambda\|,
\tag{6}
$$

where $f_{\mathrm{ref}}$ is the loss with each minimum replaced by its
reference branch. The two fitted multipliers at site $i$ are the weights of its
non-reference branches; the reference branch receives the remainder. A model is
admitted only if every site's weights are nonnegative and sum to one, so that
they form a Clarke subgradient of the hard loss [@clarke1983].

A model fits the normalized smooth branch-mixture loss with these fixed
weights on a small span $U=[u_1,\ldots,u_m]$:

$$
q(z)=\gamma^\top z+\tfrac12 z^\top H z.
\tag{7}
$$

Reduced curvature comes from central differences of fresh first gradients
[@nocedal2006], checked at two step sizes and for mixed-product symmetry.
These are numerical consistency tests, not interval bounds on the Hessian.
The model suggests a displacement, whose largest raw-coordinate change is
capped at $0.25$. Finite evaluations and Gauss--Newton corrections toward
weighted balance follow. Candidates are ranked by (3), not by the quadratic
prediction.

The directions are built in order from successive projected residuals, so the
span is nested and Krylov-like. A model of width $m$ uses the first $m$
directions of any wider model from the same origin. The model is the
subspace-restricted quadratic step familiar from truncated conjugate-gradient
and subspace trust-region methods [@steihaug1983; @nocedal2006]. This procedure
starts with a small direction set and sometimes expands it to twelve or twenty
directions. The recorded continuation also contains smaller retained models
and partial expansions, including an eleven-direction comparison. Model width
is a number of coupled directions in the full parameter space, not a search over
six or twelve individual parameters.

## 2.3 Why correction matters

For convex branch weights $w_i$, define

$$
s_i=\sum_k w_{i,k}v_{i,k}-\min_kv_{i,k}\ge0,
\qquad S=\sum_i a_i s_i.
$$

Replacing each minimum by its weighted average yields a mixture surplus
$F_{\mathrm{mix}}$ with the exact accounting identity

$$
F_\tau=F_{\mathrm{mix}}-S,
\qquad \Delta F_\tau=\Delta F_{\mathrm{mix}}-\Delta S.
\tag{8}
$$

A smooth proposal can gain mixture surplus while losing hard surplus through
branch slack. Restoration addresses that finite penalty. Equation (8) is
elementary algebra; it is not a new theorem establishing optimizer
convergence.

The overall scheme belongs to established families:

- separating directions along an active set from directions transverse to it,
  as in partial smoothness and $\mathcal{VU}$ methods [@lewis2002; @lemarechal2000; @mifflin2005];
- correcting a tangent step back to the constraint set, as in second-order
  corrections for sequential quadratic programming [@nocedal2006].

Those theories do not automatically give convergence guarantees for this
nonconvex program, and we claim none.

# 3. Observed search

The search used CPU float64 on an Apple M1 Max laptop with 64 GiB unified
memory. No GPU or cloud computation was used for the numerical search or the
recorded local certificate executions. AI systems assisted with engineering,
analysis and proof development under the author's direction. They were not the
numerical optimizer: programs generated and evaluated finite candidates, which
were checked independently before numerical promotion.

**Exploratory phase.** The campaign began with randomly initialized symmetric
level-four search and a lift of a level-three solution. It then opened
path-dependent parameters, tested fixed-block probability models, and added the
branch-aware corrections of §2. This phase ended at the numerical milestone
$2.371174031813689$.

**Negative results from that phase.** Several mathematically motivated
variants lost to ordinary optimization:

- In a matched-time control from a common checkpoint, 25 recomputed branch
  corrections gained $1.38\times10^{-6}$ in $4546$ s. Fresh Adam [@kingma2015]
  gained $7.70\times10^{-6}$ in $4552$ s.
- Repeated reduced-Newton composition gained $1.52\times10^{-6}$ in $2375$ s.
  The first Adam checkpoint at a matched or later time had gained
  $4.37\times10^{-6}$ in $2637$ s.
- In a later equal-allowance comparison, both arms timed out. Adam's completed
  checkpoints did not improve its baseline, while a saved adaptive trial was
  later validated.

These comparisons do not rank optimizers in general. They show that the
continuation's method is one workable choice in this basin, not a demonstrated
improvement over tuned first-order search.

**Continuation.** The aggregate data accompanying this paper cover 41 recorded
continuation stages with global-gain accounting, including one rejected trial.
Figure 1 shows the accepted numerical trajectory and selected endpoints. These
are sequential observations from one adaptive campaign, not independent trials.
Only the selected final endpoint received the exact certificate (1).

![Accepted numerical scores across 41 recorded continuation stages. The horizontal axis is record order, not elapsed time. Rejected stages retain the preceding incumbent. The plotted numerical endpoint is distinct from the certified claim (1).](figures/continuation.pdf){width=94%}

| Selected continuation point | Numerical score | Model width |
|---|---:|---:|
| First plotted stage | 2.3711732303548674 | 20 |
| Later matched comparison | 2.3711710779474715 | 12 |
| Subsequent matched comparison | 2.3711707343084147 | 12 |
| Partial expansion | 2.3711699581586510 | 11 |
| Later twelve-direction step | 2.3711698336026850 | 12 |
| Penultimate point | 2.3711694128460494 | 6 |
| Selected search043 endpoint | **2.3711693500058737** | **6** |

: Table 2. A subset of recorded numerical incumbents. Full plotted data are
in `data/search-progress.csv`. The first plotted stage is already below the
exploratory-phase milestone; the graph does not represent every intervening
preparation step.

## 3.1 Wider models and the cost of extra directions

Eight recorded comparisons have both a wider score and a marginal funding
calculation. Seven compare six with twelve directions; one compares six with
eleven. In each, the wider model found a lower recorded hard score from the same
origin. This is largely expected by construction. The narrower model's
directions are a prefix of the wider model's nested sequence. So whenever the
reduced Hessian is positive definite, the wider quadratic step predicts at least
as much gain. Only displacement capping and finite restoration can reverse the
order. The informative quantity is therefore cost.

A comparison was **funded** when three conditions held:

1. the extra global gain exceeded $\max(10^{-9},10u)$, where $u$ is the
   conservative readout uncertainty;
2. the extra gain per charged hour exceeded a rate floor $\rho$, preregistered
   before the comparison from the campaign's recently realized global gain per
   recorded phase hour; and
3. both widths met weighted balance $\le10^{-11}$.

Charged time is the stage's phase time minus the six-direction model span and
the six-direction trials. Shared or unassigned computation is therefore charged
to the wider model. Four comparisons were funded and four were not (Figure 2).
Two further attempted comparisons lack the required paired data and are
excluded from that count.

![Marginal wider-model gain per recorded computation hour divided by the preregistered rate floor. A ratio of one is the funding threshold. All eight wider scores improved on their matched narrow scores; only four passed this economic threshold. Comparison G has eleven directions; the others have twelve.](figures/width-efficiency.pdf){width=94%}

The floor moves with the campaign's own recent progress. It is not a
statistical significance test or a fixed mathematical property of a width.
Balance qualification and numerical promotion are separate gates; a favorable
rate does not establish an admissible candidate. The defensible observation is
that extra directions did not consistently justify their additional cost, even
when they lowered the score. The data do not show that six directions generally
beat twelve or twenty, and do not establish a universal best expansion schedule.

## 3.2 Smooth gain versus the original objective

Comparison E illustrates the point:

| Quantity at the origin of comparison E (twelve directions) | Normalized gain |
|---|---:|
| Raw proposal, mixture gain | $2.33451\times10^{-7}$ |
| Raw proposal, hard gain | $-7.98209\times10^{-6}$ |
| After restoration, hard gain | $2.34389\times10^{-7}$ |

These are changes in surplus divided by the fixed origin normalization, not
differences of numerical exponent scores. The contrast between the raw and
restored outcomes illustrates (8): an accurate prediction for a smooth mixture
alone is insufficient.

The supplied `data/model-predictions.csv` distinguishes raw mixture gain,
raw hard gain and corrected hard gain for eleven observed proposals.
Corrected steps differ from the original model displacement, so their
outcomes are not direct measures of quadratic prediction accuracy.

## 3.3 Geometry of the selected endpoint

Three recorded readouts of the final point agree at $2.3711693500058737$.
They use indexed, reference and serialized/reloaded indexed evaluations. Each
reports maximum absolute normalized weighted contrast $2.26042\times10^{-13}$.
The largest *unweighted* branch spread is instead $1.27715\times10^{-7}$, at a
root site with small weight. Root weights range from approximately
$9.97040\times10^{-7}$ to $0.436922$.

Thus the endpoint is closely balanced in the weighted objective, while not all
unweighted branch triples agree to the same tolerance. Branch balance is a
search heuristic only. The certificate checks the feasibility inequality, and
ties play no role in its validity. Numerical agreement of these readouts remains
distinct from exact rational acceptance.

## 3.4 Compute accounting

The 41 recorded continuation stages charge approximately **18.82 hours** to
newly recorded model, endpoint, reconciliation and metric-setup phases. They
also charge **17.09 minutes** of recorded numerical-review time.

- These totals include the rejected stage.
- They exclude preparation and other unavailable intervals.
- Retained models may borrow earlier work.
- They are not total CPU hours or the wall-clock duration of the research
  project.

The exploratory phase's optimizer records already contain approximately
483 process-elapsed hours, before its later derivative and certification
stages. That separate partial accounting prevents interpreting the 18.82-hour
continuation as the cost of finding the bound from scratch. The work
demonstrates feasibility of local laptop refinement and checking; it does not
establish a comparative speed advantage over GPU-based search.

# 4. Exact certification

The selected physical point was rationalized and supplied with fresh
maximum-entropy witnesses and directed logarithm enclosures. This follows the
certification scheme of Dupont et al.:

- their Lemma 1 (§2.5): a strictly positive witness $y$ with the target
  marginals and Lagrange residual $\varepsilon$ certifies
  $H(y)\le H^{\max}_D(\rho)\le H(y)+2\varepsilon$;
- their §4: exact rational evaluation with outward-rounded logarithms.

Our implementation proves the Lemma 1 bound and the directed checker sound in
Lean. Exact checking verifies the domain conditions and the sufficient
feasibility inequality at (1). The Rust and Lean implementations do not use the
numerical optimizer's floating-point score as evidence of feasibility.

The canonical certificate contains **459,013,469 bytes**, with SHA-256

```text
1a05ebc4e32c1a2121e6da2020c4321cc1d505ea2564b29e3d64eb12ee5ff521
```

The generated module is `MatrixMath.Generated.Omega_1a05ebc4e32c1a21`.
Its acceptance theorem applies to the complete literal bytes, claim and
digest. Its exponent theorem concludes (1). The exact declaration names,
elaborated statement hashes and transitive axioms are supplied in
`compiled-assurance.json`.

Two full CN executions completed on the same machine and pinned toolchain:

- the first evaluation; and
- a replay after retrieval through an initially empty local content-addressed
  store.

The replay regenerated and evaluated the whole module; it did not reuse the
first acceptance Boolean or theorem as its computation. It confirms
determinism and lossless transport, not independence from the toolchain.
Exact Rust checks, compiled theorem/axiom audits, complete trust ledgers and all
four deterministic artifact comparisons also passed.

The Rust checker is an independent implementation, but it implements the same
specification transcription as the Lean checker. A transcription error shared
by both would not be detected by their agreement (§5).

Table 3 gives command durations, including their prerequisite work.

| Check | Command elapsed (s) |
|---|---:|
| First exact Rust check | 793.11 |
| First full CN certification | 13,908.37 |
| Retrieved exact Rust check | 827.38 |
| Whole-module CN replay | 14,984.84 |

: Table 3. Result-specific checking durations. The CN commands include Rust
prerequisites, module generation, dependency work and compiled auditing;
these are not isolated Lean kernel times. The two standalone Rust checks
are separate commands, not durations subtracted from the CN commands.

Seven recorded sequential result-specific commands, including production,
exact target selection and local retrieval, total about 9.13 hours. This
excludes setup/builds, separate audits and reviews, and unknown-duration
intervals. No whole-research compute total is asserted.

# 5. Formal trust boundary

Lean [@lean4] proves the general directed checker sound and connects byte
acceptance to the defined feasibility predicate. The remaining dependencies
of the result theorem fall into three groups:

1. **Standard logical axioms:** `Classical.choice`, `propext` and `Quot.sound`.
2. **Certificate-specific native evaluation:** one `native_decide` axiom
   for the closed acceptance computation. This adds trust in the relevant
   pinned compiler, native runtime and big-integer implementation.
3. **The mathematical bridge:** `MatrixMath.AX1_combination_loss`, representing
   the combination-loss feasibility theorem [@alman2025] as stated in Dupont
   et al.'s Theorem 1 [@dupont2026]. It connects the checked feasibility
   conditions to the exponent bound. Its proof is not formalized in this
   package.

AX1 is stated for every $q\ge1$ and $\ell^*\ge2$. These restrictions are
enforced by the well-formedness predicate inside `CombinationLossFeasible`.
The axiom is only as trustworthy as the Lean transcription of Dupont et al.'s
Eq. (11). If that transcription were not faithful, AX1 could be false, and the
result theorem would not establish the bound. The fidelity of the definitions
in `lean/MatrixMath/Spec/Instance.lean` to Eq. (11) is therefore part of what a
reader must audit. `verification-source/docs/traceability.md` maps each spec
equation to its Lean definition and Rust implementation for that audit.

Lean kernel soundness is a metatheoretic assumption, not a further Lean
axiom. The result's transitive dependency list is mechanically recorded;
that transparency does not remove the assumptions themselves. Rust
agreement is independent corroboration of the computation, not of the
transcription, and not a replacement for the Lean theorem's premises. The
numerical optimizer, AI assistants and certificate producer remain outside the
result's logical authority.

Proving the bridge in Lean and replacing native evaluation by kernel-checkable
certificate acceptance would strengthen the result. Neither has been
completed for this released package. Work on those extensions does not
retroactively change this theorem's axiom list.

# 6. Independent reader verification

The matching package is `certifications/l4-2026-10-04-search043`.
Its `verification-runbook.md` separates four distinct operations:

1. Check supplied sizes, hashes and lossless theorem transport with
   `python3 verify-files.py`.
2. Build the pinned Rust and Lean source in an isolated copy.
3. Run the independent exact Rust check on the complete certificate.
4. Run full CN certification, compare the generated module and compiled
   assurance, and inspect the new runtime trust ledger.

The last two commands, from the isolated `verification-source` directory,
are

```sh
target/release/mm verify ../payloads/certificate.json --skip-lean --json
target/release/mm prove ../payloads/certificate.json --profile cn --json
```

Rust 1.94.0, Lean 4.33.0 and the supplied dependency locks fix the intended
build environment. File hashing checks identity; compilation checks source
buildability. Neither alone establishes fresh certificate acceptance.

The `verify-files.py` inventory is stored in the same package it checks. The
external trust anchors are the certificate and module digests printed in §4 and
Appendix A, together with the release tag.

The recorded runs used an Apple M1 Max with 64 GiB unified memory. Peak
whole-system memory in use was about 34 GiB during the first CN run and 37 GiB
during the replay. Both figures include roughly 20 GiB already in use by other
processes when each run started. We therefore expect about 48 GiB to suffice,
but have not tested a smaller machine. Durations are in Table 3.

The reduced reader workspace has fresh Rust and Lean source builds checked
using caches of the exact pinned external dependencies. A full certificate
execution from that reduced package with freshly downloaded dependencies
has not yet been tested. The original complete CN runs described in §4
remain the recorded mathematical acceptance evidence. A reader's new
source closure and runtime ledger must be distinguished from the original
full-source records.

The certificate and compressed theorem are separate large payloads; GitHub's
automatic source archives do not contain them. The release identifier is
`l4-2026-10-04-search043`. The associated minimal verification archive,
certificate, compressed theorem and download checksums provide the inputs
listed in the runbook. The search program and its private checkpoints are
not needed to reproduce certificate verification. The aggregate plotting
data supplied with this paper allow its descriptive charts to be examined,
but do not reproduce the private optimization campaign. Statements in §3
about the exploratory phase rest on the author's records.

# 7. Interpretation and limitations

The numerical gain comes from further refinement within the existing
level-four formulation. It is not a new asymptotic matrix-multiplication
construction or a resolution of known barriers [@ambainis2015; @alman2018limits].
The methodological observation is narrower: small tangent models, finite
restoration and adaptive investment in extra directions produced useful
progress in the observed basin. Better smooth predictions did not remove the
need to test the nonsmooth hard objective.

The campaign is adaptive and its origins are sequentially related. The record
does not include:

- a randomized multi-seed comparison;
- a proof of local or global optimality;
- a uniform curvature bound or convergence guarantee;
- an explanation for the near-uniform branch multipliers.

Earlier matched controls favored Adam. The selected endpoint's certificate does
not validate a causal account of how it was found.

What the reader can verify is the complete canonical witness, exact
feasibility acceptance and the resulting exponent theorem under the
explicit CN and combination-loss assumptions. Those boundaries make the
result independently assessable without disclosing the numerical optimizer.

# Appendix A. Artifact identities

The raw generated Lean module contains 459,016,569 bytes and has SHA-256

```text
7a2b439bed7c9caf3e3e59a0ee338b84c21efa51acacda2419448465d83f2786
```

Its lossless compressed payload is `Omega_1a05ebc4e32c1a21.lean.gz`, with
85,386,874 bytes. The package inventory binds both compressed and raw
identities. The original full normative source manifest contains 1,259
files and has SHA-256

```text
b56790ee4a5c9701f7f2f0754b870a98883fec474536ec3d23311e6b2750deed
```

This original manifest is distinct from the reduced reader workspace.
The exact claim, canonical certificate, module and assurance are matched
by the supplied inventory.

# Appendix B. Aggregate data

The paper supplies three small tables in `data/`:

- `search-progress.csv`, which retains the rejected stage and its preceding
  incumbent;
- `width-efficiency.csv`, which also keeps the two unavailable comparisons;
- `model-predictions.csv`.

Comparison labels A--H follow the order of the eight available marginal
funding comparisons; G is the eleven-direction case.

Before preparing the paper, the 140 consumed source-metadata bindings for
these tables were rehashed. That check concerns the plotted observations;
the large numerical payloads and full mathematical assurance closure were
not rerun for the charts. `data/manifest.json` binds the supplied aggregate
tables, figures and the endpoint-summary values. It contains no private
filesystem paths or numerical checkpoint archives.

# Bibliography

::: {#refs}
:::
