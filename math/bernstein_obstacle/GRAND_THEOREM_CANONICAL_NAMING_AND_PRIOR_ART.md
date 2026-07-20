# Canonical names and prior-art boundary for the Bernstein–Bézier grand theorem

Date: 2026-07-20

Status: **research naming proposal and targeted prior-art audit; not a legal or
exhaustive novelty opinion**

Canonical formal branch:
`formal/bernstein-bezier-grand-canonical`

## 1. Recommended theorem family

### Umbrella name

## Bernstein–Bézier Grand Barrier Theorem

This is the public umbrella name for the complete program:

1. exact whole-element feasibility from Bernstein–Bézier coefficients;
2. conservative lower/upper obstacle envelopes;
3. Mosco convergence of the computable inner sets;
4. convergence of constrained minimizers or variational-inequality solutions;
5. clipping-repair and multiplier rate transfer.

The name is intentionally descriptive. It should not be used to imply that every
physical Sobolev/free-boundary hypothesis is already machine formalized.

### Named component results

1. **Bézier Inner-Cone Certificate**
   
   Coefficient membership in a box or cone certifies the corresponding
   pointwise bound on the complete element.

2. **Bernstein–Bézier Barrier Envelope Theorem**
   
   Conservative sampled lower and upper envelopes define exact inner discrete
   order intervals; strong recovery plus weak closedness gives Mosco
   convergence.

3. **Bernstein–Bézier Inner-Cone Falk Theorem**
   
   Strong monotonicity, Lipschitz control, certified recovery and a
   complementarity residual yield the nonlinear/nonsymmetric recovery estimate.

4. **Bernstein–Bézier Codimension–Growth Clipping Law**
   
   A coefficient correction of amplitude `O(h^beta)` supported on a patch of
   measure `O(h^kappa)` has
   `W^{1,q}` scale `O(h^(beta - 1 + kappa/q))`.

5. **Three-Halves Contact Law**
   
   The specialization `(q,beta,kappa)=(2,2,1)` gives the interface exponent
   `3/2`.

6. **Balanced Contact Exponent Principle**
   
   The repair and multiplier mechanisms balance when
   `beta = q/(q-1)`.

7. **Bernstein–Bézier Bregman Transfer Theorem**
   
   Under two-sided Bregman `q`-growth and multiplier consistency, the interface
   exponent is
   `min(beta - 1 + kappa/q, (beta + kappa)/q)`.

## 2. Naming collision search

Targeted exact-phrase searches were run for the names above on 2026-07-20.
No mathematically relevant exact matches were located for:

- `Bernstein–Bézier Grand Barrier Theorem`;
- `Bernstein–Bézier Barrier Envelope Theorem`;
- `Bézier Inner-Cone Principle` or `Bézier Inner-Cone Certificate`;
- `Three-Halves Contact Law`;
- `Balanced Contact Exponent Principle`;
- `Bernstein–Bézier Bregman Transfer Theorem`.

This supports their use as project terminology. It does **not** prove that the
underlying mathematics is novel.

## 3. Closest known literature

### Bernstein coefficient bounds

Larry Allen and Robert C. Kirby, *Bounds-constrained polynomial approximation
using the Bernstein basis*, arXiv:2104.11819.

Known contribution:

- coefficient bounds imply polynomial bounds;
- constrained approximation is formulated as optimization;
- the construction extends to simplices.

Boundary with this project:

- this is approximation theory, not the present moving finite-element obstacle
  sets, direct Mosco recovery theorem, free-boundary clipping law, or minimizer
  transfer theorem.

### High-order bounds-satisfying finite elements

Robert C. Kirby and Daniel Shapero, *High-order bounds-satisfying approximation
of partial differential equations via finite element variational inequalities*,
arXiv:2311.05880.

Known contribution:

- abstract best approximation for finite-element variational inequalities;
- high-order `W^{1,p}` approximation by the full bounds-constrained polynomial
  class;
- Bernstein coefficient constraints proposed as a computational sufficient
  subset.

Important opening:

- the paper explicitly states that its theoretical results do not guarantee
  high accuracy for that Bernstein-coefficient subset. The direct positive
  sampling/recovery theorem for the computable subset is therefore the relevant
  collision question.

### 2026 hp/spectral obstacle method

*hp-adaptive/Spectral Element Methods for Elliptic Obstacle and Free Boundary
Problems*, Communications in Nonlinear Science and Numerical Simulation,
available online 2026-06-01, DOI `10.1016/j.cnsns.2026.110252`.

Known contribution:

- transformed GLL constraints;
- convergence of the discrete convex sets in the sense of Glowinski;
- an `O(h/N)` estimate;
- use of Bernstein positivity in the hp/SEM construction.

Boundary requiring specialist review:

- determine whether its transformed GLL construction is equivalent to any
  portion of the complete simplicial coefficient inner cone;
- the searched presentation does not state the conservative bilateral sampled
  envelopes, the exact coefficient-order interval in `W_0^{1,p}`, or the
  codimension–growth clipping law.

This is the closest current collision and must be treated prominently.

### Nonlinear obstacle finite elements

Banz, Lamichhane and Stephan, *Higher order FEM for the obstacle problem of the
p-Laplacian—A variational inequality approach*, Computers & Mathematics with
Applications 76 (2018), DOI `10.1016/j.camwa.2018.07.016`.

Known contribution:

- higher-order finite-element discretizations for the p-Laplacian obstacle
  problem;
- a priori and a posteriori estimates;
- h- and polynomial-degree convergence rates.

Boundary with this project:

- nonlinear obstacle FEM itself is not new;
- the candidate contribution is exact complete-element Bernstein certification,
  conservative bilateral envelopes, and the specific inner-cone transfer and
  clipping laws.

### Mosco stability

Boccardo, Palladino and Picerni, *Mosco-convergence of convex sets and unilateral
problems for differential operators with lower order terms having natural
growth*, arXiv:2505.05899.

Menaldi and Rautenberg, *On Some Quasi-Variational Inequalities and Other
Problems with Moving Sets*, arXiv:2106.13665.

Known contribution:

- Mosco stability of obstacle-type variational inequalities and broader moving
  convex-set theory.

Boundary with this project:

- Mosco convergence and solution stability are classical;
- the candidate new object is the specific computable Bernstein–Bézier inner
  family and its constructive recovery proof.

### Double-obstacle problems

Nonlinear double-obstacle problems and their regularity are established in the
literature; for example, *Gradient estimates for nonlinear elliptic double
obstacle problems*, Nonlinear Analysis 194 (2020), DOI
`10.1016/j.na.2018.08.011`.

Boundary with this project:

- bilateral obstacles are not new;
- the conservative coefficient envelopes and exact whole-element certified
  discretization are the candidate contribution.

## 4. Defensible novelty statement

The current defensible statement is:

> We found no exact prior source, within the targeted searches above, for the
> combined construction consisting of conservative sampled bilateral obstacle
> envelopes, exact complete-element Bernstein–Bézier coefficient certification,
> a direct strong-recovery proof of Mosco convergence for that computable inner
> family in `W_0^{1,p}`, nonlinear uniformly convex/strongly monotone transfer,
> and the parameterized codimension–growth clipping exponent.

This must be presented as **no exact collision found in the searched sources**,
not as proof that no prior result exists.

## 5. Claims that must not be called new

Do not claim novelty for any of the following in isolation:

- Bernstein convex-hull/range certification;
- obstacle or double-obstacle variational inequalities;
- Mosco convergence or Glowinski convergence;
- Falk-type estimates;
- higher-order p-Laplacian obstacle FEM;
- uniformly convex minimizer convergence;
- finite-dimensional norm scaling on a patch;
- positive-part clipping as a projection.

## 6. Eponym policy

Do not use an author-eponym such as “Dabish theorem” before independent review
and publication. If the full combined theorem survives specialist review, an
acceptable later shorthand would be **Dabish’s Bernstein–Bézier Barrier
Theorem**, while the formal manuscript title should retain the descriptive
name.
