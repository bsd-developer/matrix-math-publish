---
title: "What the Equations Are Saying: A Notation Companion to Proof-Guided Branch-Aware Search"
author: |
  BSD (bsd.developer@proton.me)\\
  Independent Researcher
date: 30 September 2026
abstract: |
  This companion explains the mathematical notation in *Proof-Guided
  Branch-Aware Search for a New Matrix Multiplication Bound*. It follows
  that paper's equations in order. For each one, it identifies the objects,
  operations, and logical status of the statement, then develops a simpler
  picture of why the expression matters. Additional equations here are
  explanatory, not new claims about the measured search or a substitute
  for its exact certificate.
---

# 1. How to read this paper

The methods paper alternates between four kinds of object. A **physical point**
$\theta$ is an assignment of distributions and scalar parameters. A **score**
such as $E(\theta)$ or $F_{\rm hard}(\theta;\Omega)$ is a number computed from
that assignment. A **proposition** such as $H_i(\xi)$ is something that could
be true or false. A **proof** such as $\pi_i$ is evidence that a particular
proposition is true. Keeping those types apart prevents the most tempting
misreading: a good numerical score is not itself a proof of a bound.

Here is the notation used repeatedly below.

| Mark | Mathematical reading |
|:---|:---|
| $g(\theta)$ | The value of the function $g$ at the parameter assignment $\theta$. |
| $g_i$, $v_{i,k}$ | Subscripts label an object or its position; $i$ is a site and $k$ is a branch. |
| $\theta_0,\theta_1$ | An origin and a proposed endpoint. A subscript $0$ does not mean zero. |
| $\theta_*,\xi_*$ | A selected, particular witness. A star is a label, not multiplication. |
| $\Delta g$ | The finite change $g(\theta_1)-g(\theta_0)$, not a derivative. |
| $\sum$, $\min$, $\max$ | Add a finite collection; take its smallest value; take its largest value. |
| $\forall$, $\bigwedge$, $\Longrightarrow$ | "For every"; "all of these hold"; "if the left side holds, then the right side holds." |
| $\lVert v\rVert^2$ | The squared Euclidean length of a vector $v$, when the chosen local coordinates are Euclidean. |
| $\underline{x}$, $\overline{x}$ | A certified lower and upper enclosure of a real quantity $x$, respectively. |

The word **hard** refers to the original objective with actual minima over
branches. **Mix** refers to a smoother weighted-mixture expression. Their
values agree only when the relevant mixture slack is zero. The word
**exact** refers to rational input and directed checking; it does not
describe a floating-point search readout.

# 2. The finite object behind the exponent

The matrix multiplication exponent $\omega$ is the unknown quantity to be
bounded. The paper fixes the Coppersmith--Winograd base parameter $q=5$ and
the maximum recursion level $\ell^*=4$ [@coppersmith1990; @alman2025]. The
star on $\ell^*$ means the chosen top level. At an intermediate level
$\ell$, a shape is a triple of nonnegative integers,

$$
(a_X,a_Y,a_Z),\qquad a_X+a_Y+a_Z=2^\ell.
$$

| Term | Precise meaning |
|:---|:---|
| $a_X,a_Y,a_Z$ | The three coordinates of a shape; each belongs to $\mathbb N_0$. |
| $2^\ell$ | The prescribed coordinate total at level $\ell$. |
| $\ell^*=4$ | The largest recursion level in this instance; it does not say that every tree node has level four. |

The tree records successive choices of regions, shapes, splits, and leaf
parameters. Its paths matter: two nodes with the same shape and level can
still represent different choices. The symbol $\theta$ collects every free
distribution and leaf parameter into one large assignment. It is a point
in a constrained parameter space $\Theta$, not merely a short vector in
the displayed equations.

One can picture a shape as an address with three entries whose total is
fixed by the floor of the tree. The parameter $\theta$ is the full set of
instructions placed at all those addresses. The rest of the paper asks
whether a particular complete set of instructions passes a stringent
inequality.

## 2.1 The fixed threshold

The methods paper abbreviates a constant:

$$
C_{q,\ell^*}=2^{\ell^*-1}\log_2(q+2)=8\log_2 7.
$$

| Term | Precise meaning |
|:---|:---|
| $C_{q,\ell^*}$ | A threshold fixed once $q$ and $\ell^*$ are fixed. Its subscripts record that dependence. |
| $2^{\ell^*-1}$ | A power of two arising from the chosen recursion level; at $\ell^*=4$ it equals $2^3=8$. |
| $\log_2(q+2)$ | Base-two logarithm of $q+2$; with $q=5$, its argument is $7$. |
| $=$ | The second expression is an exact substitution, not a numerical approximation. |

The base-two logarithm asks how many doublings are needed to reach a
number. This constant sets the height of the bar. Search changes the
assignment $\theta$; it does not move the bar $8\log_2 7$.

# 3. The feasibility inequality and the hard score

The assignment $\theta$ determines two real quantities: a retained
exponent $E(\theta)$ and a matrix-size exponent $M(\theta)$. A proposed
bound $\Omega\geq0$ must satisfy equation (1) of the methods paper:

$$
E(\theta)+\Omega M(\theta)\ \geq\ C_{q,\ell^*}.
\tag{1}
$$

| Term | Precise meaning |
|:---|:---|
| $E(\theta)$ | The retained-exponent contribution of this complete assignment. Its internal formula includes branch minima. |
| $M(\theta)$ | The matrix-size contribution of the same assignment; it also has a limiting three-way minimum. |
| $\Omega$ | A candidate numerical *upper bound* to be justified, distinct from the unknown exponent $\omega$. |
| $\Omega M(\theta)$ | Ordinary multiplication. The candidate bound is weighted by the matrix-size term. |
| $\geq C_{q,\ell^*}$ | The feasibility test: the left side must reach the fixed threshold. |

Equation (1) is not the definition of $\omega$. It is a condition in the
combination-loss formulation. The cited mathematical theorem says that a
fully feasible assignment with candidate $\Omega$ implies $\omega\leq\Omega$
[@alman2025]. That implication is a separate logical step.

For intuition, call $E$ the contribution already earned and $M$ the leverage
on the rate $\Omega$. The inequality asks whether the earned part plus the
rate-dependent part reaches the bar. This picture is useful, but the exact
definitions of $E$ and $M$ remain those of the combination-loss problem.

## 3.1 Solving for a candidate rate

If $M(\theta)>0$, ordinary algebra turns (1) into the smallest
nonnegative candidate at this particular point:

$$
\Omega_{\mathrm{hard}}(\theta)
=\max\left\{0,\frac{C_{q,\ell^*}-E(\theta)}{M(\theta)}\right\}.
\tag{2}
$$

| Term | Precise meaning |
|:---|:---|
| $\Omega_{\rm hard}(\theta)$ | The hard numerical score of the assignment. The subscript says actual branch minima are used. |
| $C_{q,\ell^*}-E(\theta)$ | The remaining shortfall after the retained contribution. |
| $/M(\theta)$ | Division by a **positive** matrix-size term; this is why the assumption $M(\theta)>0$ matters. |
| $\max\{0,\cdot\}$ | Enforces the stated restriction $\Omega\geq0$. A negative shortfall gives score zero, not a negative candidate bound. |

To derive it, subtract $E(\theta)$ from both sides of (1), then divide by
$M(\theta)>0$ without reversing the inequality. If $E(\theta)$ has already
reached the bar, the formula's zero is only a property of this feasibility
score; it is not a claim that matrix multiplication has exponent zero.

Think of (2) as a price per unit of leverage: take the gap still to be
closed and divide it by how strongly $\Omega$ acts. Search can reduce the
price by closing the gap, increasing the useful leverage, or both. It
must evaluate the *hard* expression to know whether either happened.

# 4. Why a smooth mixture can lie

At a branch site $i$, let $v_{i,1}(\theta)$, $v_{i,2}(\theta)$, and
$v_{i,3}(\theta)$ be the three competing real values. Choose weights
$w_{i,k}(\theta)\geq0$ with $\sum_{k=1}^{3}w_{i,k}(\theta)=1$. Equation
(3) defines the weighted mixture $b_i$ and its slack $s_i$:

$$
b_i(\theta)=\sum_{k=1}^{3}w_{i,k}(\theta)v_{i,k}(\theta),\qquad
s_i(\theta)=b_i(\theta)-\min_k v_{i,k}(\theta)\geq0.
\tag{3}
$$

| Term | Precise meaning |
|:---|:---|
| $i$ | A site at which three branch contributions compete. |
| $k\in\{1,2,3\}$ | The branch index at that site. |
| $v_{i,k}(\theta)$ | The value of branch $k$ at site $i$ for this assignment. |
| $w_{i,k}(\theta)$ | A nonnegative mixture weight. The three weights sum to one and may themselves change with $\theta$. |
| $b_i(\theta)$ | A convex weighted average of the branch values. |
| $\min_k v_{i,k}(\theta)$ | The branch value the hard minimum actually retains. |
| $s_i(\theta)$ | The excess of the mixture over the minimum; it is never negative under the stated weight conditions. |

Why is $s_i\geq0$? Every $v_{i,k}$ is at least the minimum $m_i$.
Multiplying these three inequalities by nonnegative weights and adding
gives $b_i\geq m_i\sum_k w_{i,k}=m_i$. This is an exact algebraic fact,
not a local approximation.

For a toy example, take branch values $(10,9,8)$ and equal weights. The
mixture says $9$, while the hard minimum says $8$, so the slack is $1$.
The average is not *wrong*; it answers a different question. The hard
problem pays attention to the weakest branch. Slack is the exact price
of looking at the average instead.

## 4.1 The ledger identity

With all site coefficients and other terms accounted for, the methods
paper writes the hard surplus at a fixed candidate $\Omega_0$ as

$$
F_{\mathrm{hard}}(\theta;\Omega_0)
=F_{\mathrm{mix}}(\theta;\Omega_0)-S(\theta;\Omega_0).
\tag{4}
$$

| Term | Precise meaning |
|:---|:---|
| $F_{\rm hard}(\theta;\Omega_0)$ | The surplus for the original minimum-based objective at fixed $\Omega_0$. Nonnegative surplus means its inequality is met, subject to domain conditions. |
| $F_{\rm mix}(\theta;\Omega_0)$ | The corresponding expression using the selected convex mixtures. |
| $S(\theta;\Omega_0)$ | Aggregate branch slack, including the relevant nonnegative coefficients. It is not just one $s_i$. |
| $\Omega_0$ | A fixed candidate rate while comparing points; the subscript $0$ here does not make it a branch index. |

The identity is *pointwise*: it holds at each represented assignment. The
weights, branch values, coefficients, and root masses can all change when
$\theta$ changes. Subtracting the identity at $\theta_0$ from the one at
$\theta_1$ gives equation (5):

$$
\Delta F_{\mathrm{hard}}
=\Delta F_{\mathrm{mix}}-\Delta S.
\tag{5}
$$

| Term | Precise meaning |
|:---|:---|
| $\Delta F_{\rm hard}$ | $F_{\rm hard}(\theta_1;\Omega_0)-F_{\rm hard}(\theta_0;\Omega_0)$. |
| $\Delta F_{\rm mix}$ | The analogous finite change in mixture surplus. |
| $\Delta S$ | The endpoint slack minus origin slack, with each point's own weights and coefficients. |
| $-$ | Exact subtraction of changes; no Taylor remainder is hidden in (5). |

~~~{=latex}
\begin{figure}[H]
\centering
\begin{tikzpicture}[node distance=15mm]
  \node[compsolid=gblue,text width=3.7cm] (mix) {mixture gain\\$\Delta F_{\rm mix}$};
  \node[compsolid=gamber,text width=3.7cm,right=of mix] (slack) {extra slack\\$\Delta S$};
  \node[compsolid=ggreen,text width=3.7cm,below=11mm of mix,xshift=2.65cm] (hard)
    {gain actually kept\\$\Delta F_{\rm hard}$};
  \draw[flow=gblue] (mix.south) -- (hard.north west);
  \draw[flow=gamber] (slack.south) -- (hard.north east)
    node[elabel,midway,right=3pt] {subtract};
\end{tikzpicture}
\caption{The branch ledger. The smooth model's apparent gain becomes hard
gain only after the change in branch slack is charged.}
\end{figure}
~~~

If the mixture gains $2$ units while slack grows $3$ units, the hard
surplus falls by $1$ unit. If slack shrinks, the hard result can improve
even when the mixture barely moves. This is why a correction that drives
branches toward equality can matter more than another nominally good
gradient step. The paper's measurements are finite and numerical; the
identity explaining them is exact.

# 5. Geometry near one point

The paper studies local directions at a validated origin $\theta_0$.
Three branches have two independent differences: for example,
$c_{i,1}=v_{i,1}-v_{i,3}$ and $c_{i,2}=v_{i,2}-v_{i,3}$. These are
**contrasts**. If both vanish, all three branch values agree. Twenty
relevant three-way sites give forty such contrasts. Collect them as a
vector $c(\theta)$, and write $J$ for its Jacobian at $\theta_0$:

$$
J=\left.\frac{\partial c}{\partial\theta}\right|_{\theta_0},
\qquad
\ker J=\{d:Jd=0\}.
$$

| Term | Precise meaning |
|:---|:---|
| $c(\theta)$ | The vector of branch differences at all tracked sites. |
| $J$ | The linear map of first derivatives of those differences at the stated origin. Its origin is part of its identity. |
| $d$ | A proposed displacement in the physical parameter coordinates. |
| $Jd$ | Predicted *first-order* change of the contrasts under displacement $d$. |
| $\ker J$ | The null space of $J$: directions with zero predicted first-order contrast change. |

A direction in $\ker J$ is tangent to the local balance conditions. It
does not promise exact balance after a finite step: curvature can bend the
path away. If $\widetilde F$ denotes the differentiable local objective,
and $P_{\ker J}$ the projection into that tangent space, the local
balanced gradient can be pictured as

$$
g_{\rm bal}=P_{\ker J}\nabla\widetilde F(\theta_0).
$$

| Term | Precise meaning |
|:---|:---|
| $\nabla\widetilde F(\theta_0)$ | Vector of first derivatives of the local smooth objective at the actual origin. |
| $P_{\ker J}$ | A projection onto the rank-checked balance tangent space. |
| $g_{\rm bal}$ | The component of the gradient available without changing tracked contrasts to first order. |

The projected gradient is an arrow on a map of the local terrain.
The tangent condition says the arrow initially travels along the ridge
where competing branches stay level. A short arrow is only a local
prediction; the finite endpoint must still be tested against the real
minimum. The paper's reported 4.594% captured squared norm means an
existing twelve-direction basis represented little of that fresh
balanced arrow's energy. It motivated more directions, not a certified
prediction of a large gain.

## 5.1 Curvature without a full Hessian

The paper estimates curvature using first gradients at displaced points.
For exposition, put $G(\theta)=\nabla\widetilde F(\theta)$. A central
difference in direction $d$ has the form

$$
H d\ \approx\ \frac{G(\theta_0+h d)-G(\theta_0-h d)}{2h},
\qquad h>0.
$$

| Term | Precise meaning |
|:---|:---|
| $H$ | The Hessian of the smooth local objective, where that Hessian exists; the method need not materialize its full matrix. |
| $Hd$ | A Hessian-vector product, the change in gradient predicted per unit displacement along $d$. |
| $h$ | A finite probe distance, not the proof-obligation symbol $H_i$. |
| $G(\theta_0\pm hd)$ | Fresh first gradients at two actual nearby physical points. |
| $\approx$ | A finite-difference estimate, not an equality or a certified interval bound. |

The scalar $d^{\mathsf T}Hd$ describes curvature along one direction.
Using two probe distances checks whether the estimate is stable under a
change of scale. It cannot prove that curvature stays bounded throughout
a finite move. In ordinary language, the method tests how the slope
changes a little ahead and a little behind, instead of building an
enormous map of every possible pair of directions. The paper also
reports why this mattered: a native second-derivative route failed a
zero-curvature diagnostic, so it was not accepted as the local oracle.

## 5.2 A finite step is a different question

A local model proposes a step $\eta d$ and perhaps a normal correction
$\delta$ to reduce branch contrasts. At the linearized level, a
zero-contrast correction would try to solve

$$
J\delta\ \approx\ -c(\theta_0+\eta d).
$$

| Term | Precise meaning |
|:---|:---|
| $\eta$ | A finite step size or fraction of a proposed displacement. |
| $\theta_0+\eta d$ | The trial physical point before correction. |
| $\delta$ | An additional displacement chosen to reduce contrast. |
| $-c(\theta_0+\eta d)$ | The change that would cancel the observed contrasts in a linear approximation. |
| $\approx$ | The Jacobian equation describes a local correction model, not exact equality at the corrected endpoint. |

The paper also describes corrections that restore inherited contrasts
rather than drive them to zero. The target matters: preserving an old
imbalance can preserve an avoidable slack bill. A correction is accepted
only after checking the full finite point, its domain constraints, and
its hard score. Geometry suggests where to try; the endpoint decides.

# 6. Proof obligations: turning one huge claim into smaller questions

Fix a rational target $\tau$ with $0\leq\tau<2.371177$. At this fixed
target, the exact surplus can be written

$$
F_\tau(\theta)=E(\theta)+\tau M(\theta)-C_{q,\ell^*}.
$$

| Term | Precise meaning |
|:---|:---|
| $\tau$ | The target bound to be established; it is fixed while the obligation is analyzed. |
| $F_\tau(\theta)$ | Left side minus right side of equation (1) when $\Omega=\tau$. |
| $F_\tau(\theta)\geq0$ | The numeric inequality needed for feasibility, in addition to all domain constraints. |

This is a useful change of viewpoint. Instead of asking directly for a
small exponent, we ask whether the exact assignment leaves a nonnegative
surplus at a chosen target. If the surplus is negative, the target fails
at that point, no matter how attractive a surrogate score looks.

The paper collects local propositions as
$\mathcal H=(H_1,\ldots,H_k)$. An extended witness
$\xi=(\theta,d,\eta,w,\ldots)$ may contain a physical point, directions,
step sizes, auxiliary weights, and other evidence. The notation
$\theta(\xi)$ means "take the physical assignment out of that larger
package." Equation (6) is a *conditional* theorem:

$$
\Pi_{\tau,\mathcal H}:\quad
  \forall \xi,\quad
  \left(\bigwedge_{i=1}^{k}H_i(\xi)\right)
  \Longrightarrow F_\tau(\theta(\xi))\geq0 .
\tag{6}
$$

| Term | Precise meaning |
|:---|:---|
| $\mathcal H=(H_1,\ldots,H_k)$ | A finite list of propositions chosen to make the target inequality derivable. |
| $H_i(\xi)$ | Obligation $i$ evaluated at extended witness $\xi$; for example, a domain, curvature, correction, or slack premise. |
| $\Pi_{\tau,\mathcal H}$ | A proof of the general implication, with the target and obligation family fixed. |
| $\forall\xi$ | The implication holds for every extended witness satisfying its premises, not merely for a sampled endpoint. |
| $\bigwedge_{i=1}^{k}H_i(\xi)$ | Every obligation must be true. One failed leaf blocks this route. |
| $\Longrightarrow$ | Logical implication. It does not assert that the premises have already been proved. |
| $\theta(\xi)$ | Projection from the extended witness to the actual physical parameters. |

This is the place where the research method becomes unusual. A theorem
like (6) does not yet lower $\omega$. It describes what evidence *would*
make the target work. The obligations are like missing pieces in a
machine: Lean can prove that, if every piece fits, the machine runs;
search and further proofs must still supply the pieces. They are
"variables" in research design because their decomposition and
thresholds may be revised, but they are logical claims, not numerical
coordinates that gradient descent can tune.

The missing pieces are genuinely useful only if they are easier to check
than the original whole claim and reveal why a candidate fails. Taking
$H_1(\xi)$ to mean "the final theorem is true" would make (6) easy to
write and useless to use.

## 6.1 Supplying the pieces

For a selected exact extended witness $\xi_*$, equation (7) shows what
must be present before the external feasibility-to-exponent theorem can
be applied:

$$
\begin{aligned}
\pi_{\rm dom}&:\operatorname{Dom}(\theta_*),
&\pi_i&:H_i(\xi_*)\quad(1\leq i\leq k),\\
(\Pi_{\tau,\mathcal H},\pi_{\rm dom},\pi_1,\ldots,\pi_k)
&\Longrightarrow \operatorname{Feasible}(\theta_*,\tau)
\Longrightarrow \omega\leq\tau .
\end{aligned}
\tag{7}
$$

| Term | Precise meaning |
|:---|:---|
| $\xi_*$, $\theta_*$ | The selected exact extended witness and its physical assignment. |
| $\operatorname{Dom}(\theta_*)$ | The conjunction of all required domain constraints on the physical assignment. |
| $\pi_{\rm dom}$ | A proof of those domain constraints. |
| $\pi_i:H_i(\xi_*)$ | A proof term whose type is obligation $i$ at the selected witness. A sampled numerical value is not such a term. |
| $\operatorname{Feasible}(\theta_*,\tau)$ | Domain conditions together with nonnegative target surplus. |
| $\omega\leq\tau$ | The desired bound, reached using the separately cited combination-loss implication. |

Read (7) from left to right as a proof assembly line. The structural
theorem says how the pieces combine. Each $\pi_i$ supplies one piece.
The domain proof ensures the physical object is legal. Only after the
assembled feasibility statement is obtained does the cited mathematical
theorem turn it into a statement about $\omega$. No assumption may be
smuggled across that last arrow.

# 7. How much improvement is actually needed?

At an origin $\theta_0$, put $M_0=M(\theta_0)>0$. The normalized
shortfall at target $\tau$ is equation (8):

$$
D_\tau
=\frac{8\log_2 7-E(\theta_0)-\tau M(\theta_0)}{M_0}.
\tag{8}
$$

| Term | Precise meaning |
|:---|:---|
| $D_\tau$ | The origin's target-surplus deficit, divided by its positive matrix-size term. |
| $8\log_2 7$ | The same fixed threshold $C_{5,4}$ from Section 2.1. |
| $E(\theta_0)+\tau M(\theta_0)$ | The left side of (1) evaluated at the origin and at target $\tau$. |
| $M_0$ | Shorthand for $M(\theta_0)$; positivity makes the division and inequality direction valid. |

The identity beneath the notation is

$$
F_\tau(\theta_0)=-M_0D_\tau.
$$

If $D_\tau>0$, the origin is below the target bar and needs a gain. If
$D_\tau\leq0$, the inequality is already met at that origin, provided
its domains are valid. Dividing by $M_0$ converts the deficit into the
same rate-like units as a change in an exponent bound. The number is not
a magic threshold: it is exactly the distance from the bar, measured
using the origin's leverage.

## 7.1 A conditional gain bound

Equation (9) is the paper's schematic finite-gain lemma. It applies only
under its stated alignment, curvature, correction, and branch conditions:

$$
\underbrace{\Delta F_{\rm hard}/M_0}_{\text{needed hard gain}}
\ \geq\
\underbrace{\eta(1-K\eta/2)\lVert v\rVert^2}_{\text{modeled mixture gain}}
-\underbrace{B_{\rm corr}}_{\text{finite correction cost}}
-\underbrace{B_{\rm slack}}_{\text{branch imbalance cost}} .
\tag{9}
$$

| Term | Precise meaning |
|:---|:---|
| $\Delta F_{\rm hard}/M_0$ | Actual finite change in hard surplus, normalized by the origin's positive $M_0$. For target closure, evaluate the surplus at the fixed target $\tau$. |
| $\eta$ | A finite step length. |
| $v$ | A chosen aligned direction in the local model; $\lVert v\rVert^2$ measures its squared size. |
| $K$ | A curvature bound required by the conditional theorem, not merely a sampled Hessian estimate. |
| $\eta(1-K\eta/2)\lVert v\rVert^2$ | A lower estimate of useful mixture gain under the lemma's hypotheses. |
| $B_{\rm corr}$ | An allowance for the loss caused by making a finite branch correction. |
| $B_{\rm slack}$ | An allowance for adverse branch-slack change. The actual slack may instead shrink. |
| $\underbrace{\cdot}_{\text{label}}$ | A visual annotation naming a term; it adds no mathematical operation. |

The factor $1-K\eta/2$ is the familiar second-order caution: the first
part of a step may help, but curvature can erode its linear promise.
The two $B$ terms charge what happens when we correct the finite move and
when the hard minimum disagrees with the mixture. Every term is expressed
in the same normalized units so it can be compared with $D_\tau$.

Here is the exact logic of the comparison. If a proved lower bound on the
right side of (9) reaches $D_\tau$, then

$$
\frac{\Delta F_{\rm hard}}{M_0}\geq D_\tau
\quad\Longrightarrow\quad
F_\tau(\theta_1)
=F_\tau(\theta_0)+\Delta F_{\rm hard}\geq0.
$$

The endpoint must still satisfy its domain conditions. Also, the paper's
sampled first gradients and finite differences suggest plausible values
for $K$ and the cost allowances; they do **not** prove the uniform real
bounds needed to instantiate (9) for the winning floating trajectory.

The picture is now simple. The origin has a debt $D_\tau$. A proposed
move promises a gross gain. Curvature, correction, and branch imbalance
send bills. Only the gain left after those bills can pay the debt. The
identity (5) tells us why the branch bill is not optional.

# 8. The last step is a check, not a search story

The paper's final result is attached to a rationalized, frozen witness,
not to the optimizer path. Let $\widehat\theta$ denote such an exact
assignment. Directed arithmetic aims to prove a safe lower bound on
the target surplus. Schematically, when the component signs permit the
displayed directions,

$$
\underline E(\widehat\theta)
+\tau\,\underline M(\widehat\theta)-\overline C\geq0
\quad\Longrightarrow\quad
F_\tau(\widehat\theta)\geq0
\quad\Longrightarrow\quad
\omega\leq\tau.
$$

| Term | Precise meaning |
|:---|:---|
| $\widehat\theta$ | A particular exact assignment, usually with rational parameters, derived from but not numerically identical to a floating point. |
| $\underline E$, $\underline M$ | Certified lower enclosures of contributions used with positive coefficients. The full checker handles each signed subterm in its required direction. |
| $\overline C$ | A certified upper enclosure of the threshold, including its logarithm. |
| $\geq0$ | A sufficient, safely rounded exact acceptance inequality. |
| $\omega\leq\tau$ | The mathematical conclusion after domain checks and the cited feasibility theorem are applied. |

The overline and underline are arrows of caution. If one wants to prove
"left side at least right side," one makes the left side pessimistically
small and the right side pessimistically large. If even that conservative
comparison passes, rounding cannot be the reason it passed. This is the
opposite of asking a floating-point display whether two nearby decimals
look ordered.

There are therefore three numbers one must not conflate: the smooth
model's prediction, the independently checked *numerical* hard score,
and the exact rational bound named by the certificate theorem. The first
guides a move. The second selects a candidate. The third, together with
the stated trust assumptions, supports the claim about $\omega$. This
companion deliberately leaves that rational unnamed: it explains the
notation, rather than replacing the result-local certificate and theorem.

# 9. One view of the whole argument

The story can be compressed into four questions, each stricter than the
last. Does a point look promising under a local mixture? Does the finite
point improve the minimum-based score after slack is charged? Can every
needed statement about an exact witness be checked? Does the resulting
feasibility theorem imply the displayed $\omega$ bound under its declared
assumptions?

The equations answer these in order. Equations (1)--(2) define what a
candidate must accomplish. Equations (3)--(5) explain why a smooth map
can mislead. The Jacobian and curvature notation say where to look next,
without pretending that a tangent or a finite difference is a finite
proof. Equations (6)--(9) turn an apparent improvement into explicit
obligations and a quantitative shortfall. The exact checker then tests
one complete frozen assignment. The profound point is also the plain
one: an optimizer may be clever about where to look, but the theorem
must still be honest about what it has actually seen.

# Bibliography

::: {#refs}
:::
