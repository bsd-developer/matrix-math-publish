---
title: "A Machine-Checked Level-Four Bound on the Matrix Multiplication Exponent: A Tie-Manifold Search Case Study"
author: |
  BSD (bsd.developer@proton.me)\
  Independent Researcher
date: "Draft updated 2 October 2026"
abstract: |
  We give an exact, machine-checked certificate for the level-four
  bound $\omega_{\mathbb Q}\le 43740440563687076465/2^{64}
  =2.37117403423113\ldots$, below the published bound $2.371177$.
  The numerical search and certification ran on a single Apple M1 Max
  laptop with 64 GiB unified memory, without GPU or cloud compute; the
  search used CPU float64. Lean 4 checks the fixed certificate, and an
  independent exact Rust checker agrees. The inference from verified
  feasibility to the exponent bound uses Alman et al.'s published
  combination-loss theorem, cited but not formalized in the released
  Lean package. We present the search as a case study: at the final
  numerical point, twenty three-way minima nearly tie, and measured
  branch-contrast gradients and fitted convex weights motivate reduced
  tangent models with finite balance corrections. An elementary
  branch-mixture identity, proved in Lean, separates surrogate gain from
  the slack paid when a move leaves the tie manifold. Proof-based tests
  also confirmed silently missing curvature in automatic differentiation.
  The native-evaluation dependencies and remaining Lean axioms are
  disclosed explicitly.

---

# 1. Introduction and result

Upper bounds on the matrix multiplication exponent $\omega$ have come, for
four decades, from the laser method [@coppersmith1990; @stothers2010;
@williams2012; @legall2014; @alman2021]. Combination loss analysis
[@duan2023; @williams2024; @alman2025] reduces the bound to a finite
optimization problem: any feasible point of its stated program yields
$\omega\le\Omega$ [@alman2025]. Alman et al. obtained
$\omega<2.371339$ at level three. Dupont et al. [@dupont2026] solved
the level-four instance with a tensor implementation and gradient-based
search, refined by AlphaEvolve [@novikov2025], and reported
$\omega<2.371177$.

We start from Dupont et al.'s level-four formulation of Alman et al.'s
combination-loss optimization problem [@dupont2026; @alman2025].
Our numerical search and exact certification ran on a single Apple M1 Max
laptop, without GPU or cloud compute. At the same level
($q=5$, $\ell^*=4$), our exact certificate and Lean theorem give

$$
\omega\ \le\ \frac{43740440563687076465}{2^{64}}
\;=\;2.37117403423113052\ldots\;<\;2.371177 .
$$

Our certified bound is approximately $2.966\times10^{-6}$ below the
published bound of [@dupont2026].
Section 6 states the theorem's assumptions and Appendix C explains how to
verify the selected certificate package. Throughout this paper, $\omega$ denotes the
rational-field matrix multiplication exponent $\omega_{\mathbb Q}$ used
in the formal theorem.

The methodological contribution is a case study of an adaptive search
trajectory and its observed behavior.
Near the best points, twenty minima over the tensor factors $X,Y,Z$
nearly tie. A smooth weighted-branch surrogate can improve while the
original objective worsens, because a move pays branch slack when it
breaks those ties. We measured this geometry, used exact identities and
conditional Lean lemmas to sharpen the experimental questions, and
searched with reduced second-order models along the approximate tie
manifold. The finite endpoints were always ranked by the original hard
score.

# 2. The level-four objective

At level $\ell^*=4$ with $q=5$, a feasible point assigns distributions
and scalar parameters to a recursion tree. Paths remain distinct even
when their shapes and regions coincide; Appendix A summarizes the
construction. Dupont et al. [@dupont2026] use Sinkhorn maximum-entropy solves
[@sinkhorn1967; @cuturi2013], implicit differentiation
[@eisenberger2022], and Adam [@kingma2015] in JAX [@jax2018]
over roughly seven million GPU parameters. Our search used PyTorch
[@paszke2019] in CPU float64 with a native maximum-entropy solver.

Let $p\in\mathcal P$ collect the free distributions and leaf parameters,
where $\mathcal P$ is a product of simplices and intervals. The numerical
search uses $n=4,664,058$ active raw coordinates $\theta\in\mathbb R^n$;
softmax and sigmoid maps, with inactive coordinates fixed, produce the
physical point $p=\Phi(\theta)\in\mathcal P$. We abbreviate
$E(\Phi(\theta))$ and $M(\Phi(\theta))$ as $E(\theta)$ and $M(\theta)$.
The exact certificate concerns the physical point $p$. For a target
$\tau$, the *surplus* is

$$
F_\tau(\theta)=E(\theta)+\tau\,M(\theta)-C,
\qquad C=2^{\ell^*-1}\log_2(q+2)=8\log_2 7 .
\tag{1}
$$

A point with $F_\tau(\theta)\ge0$ is feasible for $\tau$, and by the theorem
of [@alman2025] gives $\omega\le\tau$. When $M(\theta)>0$, the smallest
target a point supports is

$$
\Omega_{\rm hard}(\theta)=\max\Bigl\{0,\ \frac{C-E(\theta)}{M(\theta)}\Bigr\}.
\tag{2}
$$

Equation (2) is the numerical score of the search. It is computed in
floating point and is not itself a proof. §6 describes the exact check that
replaces it.

The objective's nonsmoothness comes from precisely twenty three-way
minima: six root sites, twelve interior sites, a level-two exponent
site, and a matrix-size site. Collecting terms, their explicit form is

$$
F_\tau(\theta)\;=\;g_0(\theta)\;+\;\sum_{i=1}^{20} a_i(\theta)\,
\min_{k\in\{X,Y,Z\}} v_{i,k}(\theta),
\tag{3}
$$

where the branch values $v_{i,k}$ and the remainder $g_0$ are smooth
wherever the maximum-entropy terms are. The coefficients $a_i\ge0$ are as
follows: a root weight for the six root sites, one for the twelve interior
sites and the level-two site, and $\tau$ for the matrix-size site.

The workflow in Figure 1 connects numerical search with exact checking;
§4 describes the individual steps.

~~~{=latex}
\begin{figure}[H]
\centering
\begin{tikzpicture}[node distance=6.5mm]
  \node[compsolid=gblue,text width=9.1cm] (point)
    {Independently validated point $\theta_0$ with frozen source};
  \node[compsolid=gblue,text width=9.1cm,below=of point] (geometry)
    {Contrasts $c$, Jacobian $J$, multipliers $\lambda$, tangent gradient $P_{\ker J}\nabla L_{\rm ref}$};
  \node[compsolid=gpurple,text width=9.1cm,below=of geometry] (model)
    {Tangent directions in $\ker J$; curvature from first-gradient differences};
  \node[compsolid=gamber,text width=9.1cm,below=of model] (trial)
    {Capped finite step; corrections toward $c=0$};
  \node[compsolid=ggreen,text width=9.1cm,below=of trial] (readout)
    {Hard score (2); three independent readouts; promote or reject};
  \node[compsolid=ggreen,text width=9.1cm,below=of readout] (cert)
    {Rational witness; exact directed check; Lean theorem};
  \draw[flow=gblue] (point) -- (geometry);
  \draw[flow=gpurple] (geometry) -- (model);
  \draw[flow=gamber] (model) -- (trial);
  \draw[flow=ggreen] (trial) -- (readout);
  \draw[flow=ggreen] (readout) -- (cert)
    node[elabel,midway,right=5pt] {final selected point};
  \draw[flow=gred,dashed] (readout.west) -- ++(-0.85,0)
    |- (geometry.west)
    node[elabel,pos=0.70,left=3pt] {diagnose failed move};
  \draw[flow=gpurple,dashed] (readout.east) -- ++(0.85,0)
    |- (point.east)
    node[elabel,pos=0.72,right=3pt] {accepted point: next cycle};
\end{tikzpicture}
\caption{The search cycle. Solid arrows are the path of a candidate; dashed
arrows are how finite outcomes shape the next model. Only the final frozen
witness enters the certificate check.}
\end{figure}
~~~

# 3. Local branch geometry

At the best points we measured, the twenty sites approach three-way
ties. At a model-construction point $\theta_0$, choose a minimum-attaining
reference branch $k_i^\star$ at each site. The forty normalized
*contrasts* are

$$
c_{i,k}(\theta)=\frac{a_i(\theta)\,\bigl(v_{i,k}(\theta)-v_{i,k_i^\star}(\theta)\bigr)}{M(\theta_0)},
\qquad k\ne k_i^\star,
\tag{4}
$$

collected into $c(\theta)\in\mathbb R^{40}$ with Jacobian
$J=Dc(\theta_0)\in\mathbb R^{40\times n}$. The *tie manifold* is
$\mathcal T=\{\theta\in\mathbb R^n: c(\theta)=0\}$. At any
$\theta\in\mathcal T$ where $Dc(\theta)$ has full row rank, $\mathcal T$
is locally a smooth submanifold of codimension forty, with tangent space
$\ker Dc(\theta)$ and normal space $\operatorname{range}Dc(\theta)^{\top}$.
At a measured construction point $\theta_0$ near $\mathcal T$, we use
$J=Dc(\theta_0)$ for the local tangent approximation.

## 3.1 Measurements at the selected numerical point

We measured point H, the selected numerical point with score
$2.371174031813689$, using its frozen certification source, CPU float64,
and the original active-coordinate masks. One forward evaluation and
forty contrast derivatives plus the reference gradient reproduced the saved
score, branch values, root weights and mass arrays without changing the
point. The diagnostic uses the search target $\tau=2.371170$ and the
point's fixed normalization $M_0=6.053106932142217$ in (4) and (7).

**Ties.** Across all twenty sites, the largest spread
$\max_kv_{i,k}-\min_kv_{i,k}$ is approximately $5.09\times10^{-10}$ (Figure 2a).
All twenty sites are three-way ties within both $10^{-7}$ and $10^{-8}$;
all therefore also have at least two branches within each tolerance.
Nineteen sites contribute to retained exponents and the twentieth to
matrix size, as detailed in Appendix A.

**Rank and positivity.** The forty contrast gradients have numerical rank
forty. The row-normalized Gram eigenvalues are approximately $0.0238861$ to
$3.542652$, using a relative eigenvalue cutoff of $10^{-10}$ times the
largest eigenvalue. The sixty fitted convex weights lie in
$[0.32978,0.33892]$ and are all strictly positive (Figure 2b).

**Tangent remainder.** At the same point,
$\lVert P_{\ker J}\nabla L_{\rm ref}\rVert\simeq1.557\times10^{-6}$ and
$\lVert\nabla L_{\rm ref}\rVert\simeq9.691\times10^{-2}$, a ratio of approximately
$1.607\times10^{-5}$. The reference gradient is predominantly normal to
the approximate tie manifold, with a small nonzero tangent remainder.

**Branch identities.** Between the previous model origin, point G, and
point H, the minimum-attaining branch changes at 15 of the twenty sites.
These are floating-point argmin labels among nearly tied values, rather
than persistent branch identities. The geometric quantities above concern
the numerical point; exact acceptance of its rationalized witness is a
separate check (§6).

![Branch geometry measured at the selected numerical point H. (a) Per-site branch spreads; all twenty sites meet both tie tolerances. (b) Fitted convex weights from the forty-contrast projection. Both panels use the same point and frozen source. The accompanying figure data give every branch value and fitted weight.](figures/tie-manifold.pdf){width=96%}

## 3.2 Exact mixture and branch slack

For each site choose convex weights $w_i\in\Delta_3$ and define the branch
slack

$$
s_i(\theta)=\sum_k w_{i,k}\,v_{i,k}(\theta)-\min_k v_{i,k}(\theta)\ \ge 0 .
\tag{5}
$$

Replacing each minimum in (3) by its weighted average gives a smooth
*mixture surplus* $F_{\rm mix}$, and

$$
F_\tau=F_{\rm mix}-S,\qquad S=\sum_i a_i s_i\ \ge 0,
\qquad\text{so}\qquad
\Delta F_\tau=\Delta F_{\rm mix}-\Delta S
\tag{6}
$$

for any two points, even when the weights and coefficients change between
them. This is exact algebra, not a Taylor model. It is also elementary: at a
tie, the Clarke subdifferential of a minimum of smooth functions is the
convex hull of the active gradients [@clarke1983], and (6) is the finite
version of that fact. Its use is diagnostic. A move can have positive
mixture gain and still lose if slack grows faster. On $\mathcal T$ every
$s_i$ vanishes, so $F_\tau=F_{\rm mix}$ there *for every choice of weights*.

We proved (6), the vanishing of slack at exact ties, and conditional
finite-gain corollaries in Lean for the real scalar model. These research
lemmas guide the search. They are not premises of the final theorem and are
not part of the released certificate artifact.

The multipliers enter through a normalized loss. Hold the reference
branches and weights fixed during each local model, write
$\lambda\in\mathbb R^{40}$ for the non-reference weights, and put
$M_0=M(\theta_0)$. Since
$F_{\rm mix}=F_{\rm ref}+M_0\lambda^{\top}c$, define

$$
L_{\rm ref}(\theta)=-F_{\rm ref}(\theta)/M_0,\qquad
L_\lambda(\theta)=L_{\rm ref}(\theta)-\lambda^{\top}c(\theta)
=-F_{\rm mix}(\theta)/M_0,\qquad
\nabla L_\lambda(\theta_0)=\nabla L_{\rm ref}(\theta_0)-J^{\top}\lambda .
\tag{7}
$$

Here $F_{\rm ref}$ uses the reference branch at every site. Solving
$\min_\lambda\lVert\nabla L_{\rm ref}-J^{\top}\lambda\rVert$ selects the
unique weights, when $J$ has full row rank, for which the mixture-loss
gradient lies in $\ker J$. The resulting vector is
$P_{\ker J}\nabla L_{\rm ref}$, the natural first-order stationarity measure
on the manifold. If the implied weights, $\lambda$ together with
$1-\sum\lambda$ per site, are all nonnegative, this vector is a Clarke
subgradient of the normalized hard loss at an exact tie. Its norm then
measures distance from Clarke stationarity.

Equation (6) isolates the finite penalty for departing from the
tie manifold. The identity itself is exact for the real scalar model;
the measured values of its terms are floating-point observations.

## 3.3 Geometric interpretation

Write the problem as the minimization of $-F_\tau$. Each term
$-a_i\min_kv_{i,k}=a_i\max_k(-v_{i,k})$ is then a maximum of smooth
functions. A finite sum of such terms, with linearly independent differences
of active gradients, is the standard example of a function that is partly
smooth relative to the set where the active branches tie [@lewis2002]. Along
that set the function is smooth. Across it the function is sharp, growing at
first order in every normal direction. Partial smoothness is paired with a
nondegeneracy condition: zero lies in the *relative interior* of the
subdifferential, so the multipliers are strictly positive. The measured
weights are strictly interior to the simplex. Full numerical rank, positive
fitted multipliers and a small tangent gradient at the measured points are
consistent with this interpretation; the exact hypotheses remain unproved.

Three consequences shaped the search.

1. **Surrogate gain is the wrong acceptance test.** A move with a normal
   component leaves $\mathcal T$, where $F_\tau$ is sharp and $F_{\rm mix}$
   is smooth. By (6), such a move pays branch slack at first order in the
   normal displacement. The failed finite move in §5.1 demonstrates this penalty.
2. **Branch identity is not a useful state variable.** Methods that
   differentiate through a minimum receive the gradient of one active branch.
   Near $\mathcal T$ that choice changes from step to step, which is the
   classic zig-zag of first-order methods on max-type functions
   [@burke2005]. The manifold, not the active branch, is the stable object.
3. **The right local model lives in $\ker J$.** Second-order information is
   useful along the manifold, where the objective is smooth. Across it,
   first-order restoration of $c=0$ is enough. This is the
   $\mathcal V\mathcal U$ decomposition [@lemarechal2000; @mifflin2005],
   with $\mathcal U=\ker J$ and $\mathcal V=\operatorname{range}J^{\top}$.

The problem is nonconvex, so the superlinear convergence theory for convex
$\mathcal V\mathcal U$ methods does not transfer automatically.

# 4. Branch-aware search method

The workflow in §2, Figure 1, includes feedback from finite trials:
a failed move changes the next local model. The exact checker receives
only a selected, frozen point.

## 4.1 Fresh geometry and tangent projection

Each main cycle begins at an independently validated point $\theta_0$. The
search recomputes the branch values, the forty contrasts and their
gradients (one vector–Jacobian product each), and a reference gradient. It
checks the rank of $J$ and the sign conditions on the implied weights, and
forms the tangent gradient $P_{\ker J}\nabla L_{\rm ref}$ by rank-checked
solves with the $40\times40$ Gram matrix. Every derivative is bound to the
point at which it was computed.

Derivatives are refreshed rather than transported. At one earlier point
(score $2.3711914$), a twelve-direction basis carried over from previous
cycles captured only $4.59\%$ of the squared norm of the fresh tangent
gradient. The omitted $95.4\%$ motivated expanding the basis, but it did not
by itself predict a large finite gain. Stale geometry is still useful as a
preconditioner (§4.2), but it is never described as a fresh derivative at a
later point.

## 4.2 Reduced tangent models

The method builds $m$ directions $U=[u_1,\ldots,u_m]\in\mathbb R^{n\times m}$
with $u_j\in\ker J$ to numerical tolerance; $m$ ranges from 6 to 24 in the
earlier campaign (defined in §5); the subsequent continuation used widths
6, 12 and 20 in its completed comparisons (§5.2). The directions come from
the tangent gradient, residuals of earlier reduced models, and retained
directions of previous cycles. Holding
the reference branches and $\lambda$ from (7) fixed, it fits the normalized
mixture loss $L_\lambda$ on their span:

$$
q(z)=\gamma^{\top}z+\tfrac12 z^{\top}Hz,\qquad
\gamma=U^{\top}\nabla L_\lambda(\theta_0),\qquad
He_j\approx U^{\top}\frac{\nabla L_\lambda(\theta_0+hu_j)
-\nabla L_\lambda(\theta_0-hu_j)}{2h},
\tag{8}
$$

where $e_j$ is the $j$th coordinate vector in $\mathbb R^m$. Curvature thus
comes from central differences of fresh first gradients, a standard
matrix-free technique [@nocedal2006]. Each column is computed at two step
sizes $h$. The reduced matrix is symmetrized and checked for agreement
between the two scales, scalar-slope consistency, mixed-product symmetry,
and positive definiteness before a stationary displacement is proposed.
Agreement between two scales checks the consistency of a numerical proposal.
Reduced Hessians are poorly conditioned. One model in the earlier campaign
had eigenvalues from $2.25\times10^{-6}$ to
$1.44\times10^{-3}$.

Curvature is estimated from first-gradient differences because the native
maximum-entropy backward pass did not support correct second derivatives;
§4.5 gives the proof-based test that confirmed this defect.

## 4.3 Finite steps and corrections

The positive-definite reduced loss model proposes
$z^\star=-H^{-1}\gamma$, with modeled normalized mixture gain
$-q(z^\star)$ and a cap on the maximum absolute raw-coordinate
displacement. In the earlier campaign's final step, that displacement was $0.679$ against a cap
of $0.70$, so it was not rescaled. The raw-coordinate step $Uz^\star$ is
evaluated at several bounded fractions, each mapped to a physical point by
$\Phi$. At each fraction, the search applies a bounded number of Gauss–Newton
corrections toward the manifold (up to three in the earlier campaign's final step
and up to five in the later continuation),

$$
\delta=-J^{\top}(JJ^{\top})^{-1}\bigl(c(\theta)-c^{\rm target}\bigr),
\tag{9}
$$

with domain checks on every represented parameter. The choice of
$c^{\rm target}$ is informed by the slack identity (§4.5). Early
experiments restored the contrasts inherited from the origin,
$c^{\rm target}=c(\theta_0)$. That preserved whatever slack the origin
carried. Later experiments used $c^{\rm target}=0$ wherever the implied
weights were valid convex weights. A first-order correction does not
guarantee that the endpoint is balanced or better, so every corrected
endpoint is re-evaluated.

All corrected and uncorrected endpoints compete on the hard score (2). Model
gain, residual contrast, and slack are recorded as explanations, not as
selection criteria.

## 4.4 Promotion

A candidate that improves the hard score is read three times:

- by the production evaluator, with 400 maximum-entropy iterations;
- by an independently implemented reference evaluator, with 1,600
  iterations;
- by the production evaluator again, after serialization and reload.

An independent process then reconstructs the move, the score components,
site values, root weights, masses, and the selection. Only then is the point
a *validated numerical incumbent*. The final selected point passed all
three readouts. The selected point is then
rationalized and frozen for exact certification (§6). No gradient,
curvature estimate, or research lemma enters the final theorem.

## 4.5 Proof as a design instrument

Lean supplied test oracles and made the conditions of proposed search
steps explicit.

**A proved zero-penalty identity supplied a curvature test oracle.** On 54 split
domains whose feasible law is fixed by its marginals, the maximum-entropy
penalty is identically zero, so its second derivative along any path must
vanish. On one such domain, double backward returned
$0.7213=1/(2\ln2)$, while a central second difference returned
$2.2\times10^{-11}$. The native solver's custom backward returned the
correct first derivative but treated it as a constant, silently omitting
maximum-entropy curvature on the second pass. This test confirmed the missing-curvature defect first identified by code
inspection of the custom backward pass, which used a saved gradient detached
from its input, and motivated using finite differences of fresh first gradients. A correct direct
Hessian–vector product [@pearlmutter1994] would require implicit
second differentiation through the solver's optimality conditions
[@eisenberger2022].

**The elementary identity (6) organized acceptance and diagnosis.**
Writing slack as a separate term made failed moves interpretable and
kept endpoint selection focused on the hard score rather than model gain.
The identity is an accounting tool, rather than a new optimization theorem.

**Zero slack at ties changed the correction target.** Exactly balanced
branches have zero slack. A conditional lemma bounds the hard gain of a
finite move from below,

$$
\frac{\Delta F_\tau}{M_0}\ \ge\
\underbrace{\eta\bigl(1-\tfrac{K\eta}{2}\bigr)\lVert v\rVert^2}_{\text{modeled mixture gain}}
-\underbrace{B_{\rm corr}}_{\text{correction cost}}
-\underbrace{B_{\rm slack}}_{\text{slack change}} ,
\tag{10}
$$

where $v$ is the tangent direction and $\eta$ the step. $K$, $B_{\rm corr}$,
and $B_{\rm slack}$ are explicit premises: a curvature bound, a correction
bound, and a slack bound. Sampled gradients suggest values for them but do
not prove them. What (10) made visible is that restoring *inherited*
contrasts keeps $B_{\rm slack}$ at the origin's value, whereas targeting
zero contrast can make it negative. The zero-contrast experiment in §5.1 tested that distinction.

**Orthogonality clarified basis expansion.** If a represented gradient
component and an omitted one are orthogonal, the omitted norm does not
reduce the represented slope. Omitted energy is therefore a reason to add
directions, not a penalty on the direction already chosen.

These lemmas identify which quantity to measure next and which target to
correct toward.

# 5. Experimental evidence

The experiments comprise an earlier campaign and subsequent continuation.
Here, the *earlier campaign* means the bounded eight-hour branch-aware search
from the zero-contrast correction point to numerical score
$2.371176825455252$; the subsequent continuation is reported in §5.2.
Each expensive trial began at an independently validated checkpoint and
recorded its source, origin, prediction, finite-trial controls and hard-score
readout. Both phases ran on one Apple M1 Max laptop with 64 GiB unified
memory, on CPU in float64 with one numerical worker thread. No GPU or
cloud compute was used. Recorded optimization runs total approximately
483 process-elapsed hours, a partial sum that excludes later derivative,
model-building and certification work (Appendix B).

Dupont et al. report approximately five hours on a single GPU per candidate
optimization-program evaluation in their AlphaEvolve search
[@dupont2026, §3.3]. Our eight-hour earlier campaign covers multiple model
steps, corrections and unsuccessful trials, rather than one program
evaluation. Appendix B records that campaign and the available partial
optimizer costs; §6 records exact certification costs separately.
The result demonstrates that refining and machine-checking this level-four
bound is feasible on a consumer laptop.

## 5.1 Three tests that changed the search

**A surrogate gain paid for by slack.** In the finite-slack experiment, an
uncorrected finite move gained $1.34\times10^{-6}$ in normalized
mixture surplus, but branch slack rose by $2.95\times10^{-6}$.
The hard surplus therefore fell, as the exact identity (6) requires.
Three finite corrections preserved essentially all the mixture gain
while removing the excess slack. This falsified mixture gain as an
acceptance criterion for these moves.

**Correcting inherited slack.** The zero-contrast experiment changed the target
from the origin's contrasts to zero where the implied weights were
valid convex weights. Its validated score improved by
$2.61\times10^{-7}$, almost entirely through slack removal;
mixture gain was only $1.1\times10^{-11}$. The conditional Lean
lemma (10) suggested the test.

**A reduced model that predicted a finite gain.** The model
expanded an inherited six-direction basis to twenty-four directions.
It used 73 full forward evaluations, 72 first-order vector–Jacobian
products, and no double backward; peak memory was 26.3 GB. Against
a predicted gain of $1.4868\times10^{-6}$ from its construction
point, the measured gain was $1.3990\times10^{-6}$, 94% of the
prediction. This 40-minute stage produced the earlier campaign's endpoint.

## 5.2 Trajectory and model-width choices

Appendix B gives the earlier trajectory leading into the late sequence below.

From the earlier campaign's starting point to its numerical endpoint,
the validated score fell by about $1.26\times10^{-5}$. New tangent
directions were needed after slack cleanup; repeated correction
alone did not account for the later gains. The original objective,
not the reduced model, selected every promoted point.

The subsequent accepted sequence is shown below. A restoration can serve as
a model-construction seed without becoming the global incumbent; accepted
scores must therefore be distinguished from improvement relative to a seed.

| Accepted point | Numerical $\Omega_{\rm hard}$ | Recorded source of improvement |
|---|---:|---|
| point A | 2.3711754347806533 | Fresh tangent model |
| point B | 2.3711754123857607 | Fresh model from a point restored closer to ties |
| point C | 2.3711753608722477 | Fresh tangent model |
| point D | 2.3711747196635273 | Matched-width model and corrections |
| point E | 2.3711747159935173 | Current-Jacobian balance restoration |
| point F | 2.3711741392432755 | Matched twelve/twenty-direction model |
| point G | 2.3711740797278047 | Twelve-direction continuation |
| point H | **2.371174031813689** | Twelve-direction continuation |

: Later independently validated numerical incumbents. These floating-point
scores are distinct from the exact certified claim in §6.

The decrease from point A to point H is approximately $1.403\times10^{-6}$.
About $86.8\%$ occurred in the point C–D and point E–F
transitions. At the point E origin, twelve directions reached $2.37117423209488$;
twenty directions reached $2.3711741392432755$. The extra directions helped
numerically, but their conservative marginal gain per recorded computation
hour fell below the preset minimum gain per hour. Subsequent cycles used
twelve directions.

## 5.3 Recorded optimizer controls

In an earlier comparison from the same starting point, Adam beat a
first-order bundle/headroom corrector with nearly equal runtimes. That
corrector did not use the reduced second-order tangent models of §4.2.

| Method | Common origin $\Omega_{\rm hard}$ | Recorded runtime (s) | Last measured hard score |
|---|---:|---:|---:|
| Bundle/headroom corrector | 2.3713403708334013 | 4546.10 | 2.371338993431329 |
| Fresh Adam | 2.3713403708334013 | 4551.90 | 2.3713326744345458 |

: Both methods used the same starting point and nearly equal runtimes;
Adam's listed score was last measured at 4,365 s.

A later comparison started Adam and a search using fresh projected gradients
with balance corrections from the same point (score $2.3711899235254914$),
allowing 1,100 s each; both stopped before completing their planned steps.
The last saved corrected score was $2.3711897212798734$; Adam's was
$2.3712622190785293$, worse than the starting point. These partial results
cannot be compared at exactly equal elapsed times.

A static block preconditioner improved its origin but lost to the
same-origin fresh-model control, and two structured perturbations lost
to unperturbed continuation. These mixed controls motivate reporting the
methods as an adaptive case study. Appendix B collects the compute costs.

# 6. Exact certification of the selected point

The selected numerical point has score $2.371174031813689$. Its physical
parameters were rationalized with 64-bit precision, and fresh
maximum-entropy witnesses were constructed. The canonical certificate has
**458,921,565 bytes** and SHA-256

```text
dfcede72c9dbf8eaf7b55f34cdd56d93dca7fe8a28fca2787466bec410f1873f
```

A directed exact checker verifies the domain conditions, maximum-entropy
enclosures and the sufficient feasibility inequality (1) for

$$
\Omega=\frac{43740440563687076465}{2^{64}}
       =2.37117403423113\ldots.
$$

$$
\frac{2371177}{10^6}-\Omega
 =\frac{854824676828237063}{288230376151711744\cdot10^6}
 \approx2.96577\times10^{-6}.
$$

The difference between the certified claim and the printed numerical score
is approximately $2.41744\times10^{-9}$. It includes rationalization and
outward certification bounds; it is not an estimate of floating-point error
or a measurement of rationalization alone.

The generated module is `MatrixMath.Generated.Omega_dfcede72c9dbf8ea`.
Its acceptance theorem checks the complete literal certificate bytes, claim
and digest. Its exponent theorem, `omegaResult_dfcede72c9dbf8eaf…`, states
$\omega_{\mathbb Q}\le\Omega$ for the definitionally specified rational-field
exponent. The complete declaration names, elaborated statements and their
hashes are supplied in `compiled-assurance.json` (Appendix C).

**Trust boundary.** Profile CN evaluates the closed acceptance computation
natively. Its compiled theorem depends on one certificate-specific
`native_decide` axiom. The exponent theorem additionally depends on
`MatrixMath.AX1_combination_loss`, which supplies the mathematical bridge
from the checked feasibility conditions to the bound on $\omega$.
That bridge implements the cited combination-loss theorem [@alman2025]
but is not proved within the released Lean package. Both statements also
use `Classical.choice`, `propext` and `Quot.sound`. CN trusts the relevant
pinned compiler, native runtime and big-integer implementation; Lean kernel
soundness is a metatheoretic assumption. This is not an axiom-free or
kernel-only proof. A separately implemented exact Rust checker accepts the
same certificate as an independent cross-check, not as a replacement for
the Lean theorem.

Two full CN executions completed on the Apple M1 Max laptop with Lean
4.33.0 and GMP 6.3.0: the initial proof and a new evaluation after retrieval
from an initially empty local content-addressed store. Their complete
`prove` commands took 14,468.57 s and 14,521.79 s (approximately four hours
each), including the Rust prerequisite, generation, dependency work and
compiled auditing. Standalone Rust checks took 813.53 s initially and
825.72 s after retrieval. These are command durations, not isolated Lean
kernel times or complete research costs. Strict compiled-statement and
axiom audits, complete trust ledgers and four deterministic artifact-byte
comparisons passed. The second computation was a new whole-module
execution, rather than reuse of the first acceptance result.

Appendix C gives the matching source identities and reader instructions. Removing the project
axiom and replacing native evaluation with kernel-checkable full-certificate
acceptance are ongoing work; neither strengthening is claimed here.

# 7. Implications and limitations

The exact check establishes a feasible level-four point; the exponent bound
follows from Alman et al.'s published combination-loss theorem, represented
by the unproved Lean bridge disclosed in §6. The search case study connects
near-tie geometry with practical tangent models and finite corrections;
proof-based tests supplied exact accounting and confirmed a derivative defect.
The published level-three and level-four values differ by about
$1.6\times10^{-4}$, so further numerical refinement operates on a much
smaller scale. Dupont et al. suggest that larger improvements likely require
new mathematical ideas. Known barriers for analyses based on the
Coppersmith–Winograd tensor exclude $\omega=2$ by such methods
[@ambainis2015; @alman2018limits; @christandl2021].

**Limitations.** This is one adaptive search trajectory, with local controls
rather than a systematic comparison of optimizers. Geometry was measured at
a few points in one basin; full rank, positivity and partial smoothness have
not been proved for the exact point. Curvature was sampled, not bounded,
and the conditional finite-gain lemmas were not instantiated on the winning
trajectory. The certificate validates the selected endpoint, not its search
history. No local or global optimality, convergence rate, or general
optimizer superiority is claimed.

**Open questions.**

1. *Which local geometry transfers beyond this basin?* The branch-weight
   investigation in Appendix E found no construction-specific explanation
   or demonstrated gain from imposing equal weights.
2. *Can the tie manifold be parameterized directly?* Forty equality
   constraints on 4.66 million coordinates remove little dimension, but an
   explicit chart of $\mathcal T$ would turn the problem into smooth
   optimization and might make level five tractable.
3. *Can local optimality be certified?* On a partly smooth, nondegenerate
   point, second-order conditions on $\ker J$ give a local optimality
   criterion. An exact version would bound what further local search at
   this level can achieve. It would not bound global search.

# Appendix

## A. Level-four construction and notation

Fix the Coppersmith–Winograd parameter $q=5$ and recursion level $\ell^*=4$.
A level-$\ell$ shape is a nonnegative integer triple with coordinate sum
$2^\ell$. The root chooses a region and a shape. Positive internal nodes
choose regions and admissible splits, zero-shape nodes carry split
distributions, and positive level-two leaves carry one scalar parameter.
Distinct paths remain distinct even when their levels, shapes, and regions
coincide. The complete statement is that of [@alman2025], in the form given
by [@dupont2026]. Our mathematical specification transcribes it clause by
clause, and the certificate checker of §6 decides it exactly.

The twenty minimum sites in (3) have the following accounting:

| Site class | Count | Coefficient $a_i$ |
|---|---:|---|
| Root regions | 6 | Corresponding root weight |
| Level-three regions | 6 | 1 |
| Level-four regions | 6 | 1 |
| Level-two exponent $E_2$ | 1 | 1 |
| Matrix-size exponent $M$ | 1 | Target $\tau$ |

: Minimum sites in the level-four objective.

The physical point $p$ consists of distributions and leaf scalars.
The raw search coordinates $\theta$ are mapped to $p=\Phi(\theta)$
by softmax and sigmoid maps, with inactive coordinates fixed.
The score (2) is only defined by the displayed quotient when
$M(\theta)>0$; exact domain checks are part of certification.

## B. Earlier trajectory, record mapping and compute costs

The late point A–H sequence appears once, in §5.2. Earlier selected points
are listed here.

| Stage | Validated $\Omega_{\rm hard}$ | What the step tested |
|---|---:|---|
| Lift of level-three point | 2.372151067 | First level-four point, symmetric parameterization |
| Distinct-path parameter search | 2.3713528479 | Per-path untied parameters |
| Continued distinct-path Adam search | 2.3712878268 | Continued from the distinct-path point |
| Twelve-direction model | 2.3711914229 | Twelve-direction tangent model with corrections |
| Fresh omitted-direction step | 2.3711912647 | Finite step in a freshly measured omitted direction |
| Finite-slack experiment | 2.3711899235 | Six fresh tangent directions |
| Zero-contrast correction | 2.3711894607 | Corrections toward zero contrast |
| Campaign, first cycle | 2.3711879899 | Fresh tangent model after zero-contrast correction |
| Campaign, model union | 2.3711877592 | Union of same-origin models |
| Campaign, fresh geometry | 2.3711859220 | New incumbent after refreshed geometry |
| Campaign, basis expansion | 2.3711826240 | Expanded tangent basis |
| Campaign, retained metric | 2.3711777689 | Six-direction parent of the final model |
| Capped twenty-four-direction step | 2.3711768255 | 24-direction model, three corrections |

: Selected validated numerical points. Floating-point scores; the certified
bound is in §6.

**Compute costs.** The earlier campaign defined in §5 took
8 h 08 min 05 s, including 1 h 31 min 02 s of unsuccessful stages and repairs.
Its method-family accounting is:

| Method family | Elapsed, including failures | Recorded improvement |
|---|---:|---:|
| Fresh tangent models and same-origin model unions | 2 h 21 min | $7.31\times10^{-6}$ |
| Static block preconditioning | 18 min | 0 |
| Structured perturbations with unperturbed control | 23 min | $7.7\times10^{-8}$, all from control |
| Preconditioned continuation, recovery and extensions | 4 h 34 min | $5.25\times10^{-6}$ |

: Aggregate costs by campaign stage, rounded to minutes. The remaining
elapsed time includes planning, reporting and gaps between stages. This
timing ends before the late point A–H continuation.

The available optimizer records contain approximately 483 process-elapsed
hours; the union of their recorded start/end windows covers about 277 hours.
These are partial process durations and overlapping-window coverage, not CPU
time or end-to-end research cost. Later derivative, model and certification
stages use separate records and are excluded. Whole-research elapsed and
CPU totals remain unknown. Section 6 gives the selected certificate's
checking durations separately.

**Mapping to the research record.** These identifiers are retained solely
for locating the original files; the paper uses descriptive labels.

| Paper label | Internal record identifier |
|---|---|
| Point A | best008; fresh tangent cycle 006 |
| Point B | best009; fresh tangent cycle 007 |
| Point C | best010; fresh tangent cycle 008 |
| Point D | best011; matched-width cycle 009 |
| Point E | best012; current-Jacobian restoration |
| Point F | best013; width comparison cycle 010 |
| Point G | best014; narrow continuation cycle 011 |
| Point H, selected numerical point | best015; narrow continuation cycle 012 |
| Distinct-path parameter search | P575 |
| Continued distinct-path Adam search | P1950 label; symmetric-basin campaign control at update 2000 |
| Twelve-direction model | 0141 |
| Fresh omitted-direction step | 0151 |
| Finite-slack experiment | 0154 |
| Zero-contrast correction | 0157 |
| Capped twenty-four-direction step | 0181 |

## C. Selected package and reader verification

The matching package is
`certifications/l4-2026-10-01-best015`.
Its `verification-runbook.md`
and `trust-boundary.md`
are the authoritative reader instructions for this certificate.

The result identities are:

- Certificate: 458,921,565 canonical bytes, with the SHA-256 in §6.
- Generated Lean module: 458,924,665 raw bytes. Its raw SHA-256 is:

  ```text
  71d36d830605c27c77ae116ba37a091241db4feb9a1ce746bf4772160cf289a2
  ```

  Compressed payload: `Omega_dfcede72c9dbf8ea.lean.gz`.

- Original frozen normative source manifest: 1,243 files, SHA-256:

  ```text
  668e1f1c6f0bfbdfabe840b6162cda4efebe79d59b0c528f966ab3b0e9ef6fee
  ```

- Original Lean source closure recorded in `assurance.json`:

  ```text
  0b7add6f623b0254565d2f18bfe9d29253b16c3467153c3d3de62073ecccef66
  ```

The reduced reader workspace is distinct from those original full-source
identities. Its inventory identifies unchanged checker/proof sources and
package-specific build wrappers. Its Cargo lock matches the included
workspace and retains the recorded dependency versions and checksums;
`lake-manifest.json` fixes the Lean dependencies. A reader's new source
closure and runtime trust ledger must be recorded separately.

1. **Check identity.** With `certificate.json` and the compressed theorem
   in `payloads/`, run `python3 verify-files.py` in the certification
   directory. It checks sizes, hashes and lossless theorem transport.
   A successful identity check is not mathematical acceptance.
2. **Build in an isolated copy.** Follow the runbook using Rust 1.94.0,
   Lean 4.33.0 and the supplied dependency locks. Build the Rust CLI and
   Lean checker/soundness modules. Do not regenerate dependency locks to
   bypass a failure. Building these modules does not evaluate the selected certificate.
3. **Run the independent exact check.** From the copied verification-source
   directory, run
   `target/release/mm verify ../payloads/certificate.json --skip-lean --json`.
   Require a successful exit, the matching hash and exact rational claim,
   and `rust_cross_check: ok`.
4. **Run full CN certification.** Run
   `target/release/mm prove ../payloads/certificate.json --profile cn --json`.
   Require successful full evaluation and compiled auditing. Compare the
   regenerated module's raw hash with the inventory, and compare compiled
   declaration kinds, statements, statement digests and transitive axioms
   with the supplied assurance. Review the new execution's trust ledger.

## D. AI assistance

AI systems were used substantially for engineering, analysis, proof
development and LaTeX writing, under the author's direction. This
assistance is distinct from the numerical optimization loop: AI systems
helped design, implement and analyze experiments, while search programs
evaluated and ranked candidates using the hard objective and independent
checks. The agents' outputs were treated as proposals and passed the same recorded
checks as any other search artifact. No claim depends on who, or what, wrote
the search code: the bound rests on the certificate and the checker
under the disclosed trust assumptions. A reconstruction of the working instructions is
given in the supplementary material.

## E. Near-uniform weights: an inconclusive investigation

A study of stored branch-gradient systems examined the near-uniform fitted
weights using alternative linear solvers, consistent reference-branch
rebasing and moderate block metrics. The pattern persisted under those
controls, but its cause remained unexplained. Fitted Euclidean projection
weights can depend on the coordinate metric away from exact stationarity;
forcing equal weights left additional normal-gradient residual. A positive,
full-rank stationary synthetic example with unequal weights refuted a
universal explanation based on ties and positivity alone. Global tensor
symmetry does not force equal weights at asymmetric points. The study found
no construction-specific theorem, no justified reduction to equal weights,
and no demonstrated improvement from imposing them.

# Bibliography

::: {#refs}
:::
