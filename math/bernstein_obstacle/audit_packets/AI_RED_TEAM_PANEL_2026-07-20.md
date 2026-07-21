# Bernstein–Bézier Grand Theorem: adversarial AI review panel

Date: 2026-07-20

Status: **internal role-separated AI review, not an independent human report**

This report deliberately separates mathematical validity, novelty, formal
faithfulness and computational evidence. A PASS here means that the argument is
internally defensible under its explicit assumptions. It does not replace
external peer review.

## Executive verdict

| Panel | Verdict | Main conclusion |
|---|---|---|
| Numerical analysis / Mosco | PASS AFTER CORRECTION | The fixed closed-convex-target recovery proof is sound under the positive-sampling and conformity assumptions, but general finite-element Mosco convergence for pointwise convex constraints is established prior art. |
| Free-boundary / rate | PASS AFTER CORRECTION | The exponent algebra is correct. The sharp branch must retain local quasi-uniformity, coefficient-distance localization, patch-measure and multiplier-density hypotheses. |
| Formal methods | PENDING EXACT-HEAD AUDIT | The new finite convex-target certificate is now represented in Lean source; no certification claim is allowed until the pinned build and axiom transcript pass. |
| Novelty | NARROW PASS | The convex-hull certificate and broad convex-set Mosco theory are not new. The potentially new contribution is the fixed-degree Bernstein coefficient inner-cone recovery plus the explicit repair/duality rate law and its obstacle specialization. |
| Computation | PASS AS EVIDENCE | The deterministic reproduction and independent assembly comparison pass their encoded checks. They do not prove the analytical theorem. |

---

## Panel A — numerical analysis and Mosco recovery

### A1. Exact inner inclusion

**PASS.** A complete Bernstein field is a convex combination of its coefficient
vectors. Coefficient membership in a convex target `C` therefore implies
pointwise membership in `C` on the complete simplex.

This fact is classical Bézier convex-hull theory and is not itself a novelty
claim.

### A2. Closedness of the continuous constraint

For

\[
K_C=\{v\in W_0^{1,p}(\Omega;\mathbb R^m):v(x)\in C\text{ a.e.}\},
\]

with `C` closed and convex, strong `W^{1,p}` convergence gives strong `L^p`
convergence and an almost-everywhere convergent subsequence. Closedness of `C`
passes feasibility to the limit. Hence `K_C` is norm closed and convex, and
therefore weakly closed.

**PASS.** No reflexivity is needed for the closed-convex-implies-weakly-closed
step, although reflexivity is useful elsewhere in minimizer compactness.

### A3. Smooth `C`-valued density

Assume `0 in C` and homogeneous trace. Zero extension preserves `C`-valuedness.
Convolution with a nonnegative kernel preserves membership in a closed convex
set because the convolution is a barycentric average. Multiplication by a
cutoff `0 <= chi <= 1` preserves membership because

\[
\chi y=(1-\chi)0+\chi y.
\]

A standard coupled cutoff/mollification schedule yields compactly supported
smooth `C`-valued fields converging in `W^{1,p}`.

**PASS AFTER CORRECTION.** The manuscript should explicitly specify the order
and scales of cutoff and mollification, rather than saying merely “mollify and
cut off.” For nonzero boundary data or `0 notin C`, a compatible `C`-valued
lifting and translation are required.

### A4. Positive Bernstein sampling

For a smooth compactly supported field, sample at the degree-`r` barycentric
lattice. Shared face lattice points must be represented by the same global
degree of freedom. Fixed degree `r >= 1`, shape regularity and affine
reproduction give convergence in `W^{1,p}`.

**PASS UNDER EXPLICIT ASSUMPTIONS.** The theorem must state:

- fixed polynomial degree `r >= 1`;
- uniform shape regularity;
- globally consistent orientation/assembly of shared face coefficients;
- eventual separation of the compact support from boundary coefficient points;
- a uniform physical-element positive-sampling estimate.

### A5. Novelty correction

General density and finite-element Mosco convergence for pointwise convex
constraints are prior art. In particular, Hintermüller–Rautenberg–Rösel (2017)
proved density and Mosco results for several finite-element convex constraint
sets in `L^2`, `H^1` and `H(div)`, including vector and derivative constraints.
Menaldi–Rautenberg (2021) surveys Mosco convergence for moving sets and finite
element approximations.

Therefore the paper must not claim to introduce convex-target Mosco theory.
The narrower candidate contribution is the proof for the practical
fixed-degree **Bernstein coefficient inner subset**, together with the
constructive recovery and the contact-rate mechanism.

---

## Panel B — free-boundary localization and rate

### B1. Projection repair

Project each globally assembled coefficient once onto `C`. In finite-dimensional
Euclidean coefficient space, metric projection onto a nonempty closed convex
set exists, is unique, lands in `C`, fixes `C`, and is nonexpansive.

If

\[
\operatorname{dist}(b_i,C)\lesssim h_\Gamma^\beta
\]

on a locally quasi-uniform affected patch of measure

\[
|\omega_h|\lesssim h_\Gamma^\kappa,
\]

fixed-degree norm equivalence and affine inverse scaling give

\[
\|d_h\|_{L^q}\lesssim h_\Gamma^{\beta+\kappa/q},
\qquad
\|\nabla d_h\|_{L^q}\lesssim
h_\Gamma^{\beta-1+\kappa/q}.
\]

**PASS AFTER CORRECTION.** This is not valid on an arbitrary anisotropic mesh
without a replacement anisotropic scaling theorem. The paper must also state
whether `h_Gamma` is the maximum, minimum or representative local diameter on
the affected patch.

### B2. Dual consistency

If the normal multiplier/residual has a local density bounded by
`O(h_Gamma^sigma)`, the correction amplitude is `O(h_Gamma^beta)`, and the
patch measure is `O(h_Gamma^kappa)`, then

\[
\langle\lambda,d_h\rangle
\lesssim h_\Gamma^{\beta+\kappa+\sigma}.
\]

**PASS ONLY UNDER THE DENSITY/PAIRING HYPOTHESIS.** For a measure-valued
multiplier, a boundary multiplier, or a multiplier acting on derivatives, the
same formula does not follow automatically. Each physical application needs a
separate pairing lemma.

### B3. Combined exponent

Given a genuine `q`-growth Falk/Bregman estimate,

\[
\|u-u_h\|_X
\lesssim h^s+h^r+h_\Gamma^\gamma,
\]

where

\[
\gamma=\min\left\{
\beta-1+\frac\kappa q,
\frac{\beta+\kappa+\sigma}{q}
\right\}.
\]

The balance equation gives

\[
\beta_*(q,\sigma)=\frac{q+\sigma}{q-1}.
\]

**PASS.** The algebra is correct. The notation must distinguish the Sobolev
integrability exponent from the energy-growth exponent if they differ in a
nonlinear application.

### B4. Three-halves specialization

For `q=2`, `beta=2`, `kappa=1`, `sigma=0`, both branches equal `3/2`.

**PASS.** The exact phase-locked integral proves sharpness for that clipping
repair family. It does not prove a universal lower bound over all admissible
finite-element spaces, recovery maps or discrete minimizers.

---

## Panel C — formal statement faithfulness

### C1. Existing formal core

The repository has explicit structures and theorems for:

- scalar and simplicial coefficient certificates;
- shared-face conformity and boundary localization;
- abstract Mosco recovery;
- translated moving constraints;
- Hilbert minimizer and strongly monotone VI endgames;
- integer codimension scaling and consistency saturation;
- quadratic-contact rate transfer;
- the phase-locked exact lower model.

### C2. New convex-target finite layer

`ConvexConstraint.lean` now adds:

- `simplexVectorFieldNat`;
- `simplexVectorFieldNat_mem_convex`;
- `simplexVectorFieldNat_pointwise_feasible`;
- `convex_convexCoefficientSet`;
- `smul_mem_convex_of_zero_mem`;
- abstract coefficientwise-repair feasibility.

These declarations formalize the finite convex-hull certificate and cutoff
algebra. They do not formalize Bochner convolution, physical Sobolev spaces or
metric projection existence.

### C3. Verdict

**PENDING EXACT-HEAD AUDIT.** The source should be described as a formalization
candidate until:

1. the pinned complete build succeeds;
2. `GrandCanonicalAudit.lean` runs;
3. the transcript contains all terminal declarations;
4. no `sorryAx` appears.

Even after those checks pass, the physical `W^{1,p}` theorem remains a formal
reduction from explicit analytical hypotheses, not a kernel proof of the full
PDE theorem.

---

## Panel D — novelty and attribution

### D1. Established prior art

The following are not new:

1. Bernstein/Bézier convex-hull and coefficient range certificates.
2. Bounds-constrained polynomial approximation using Bernstein coefficients.
3. High-order finite-element variational inequalities for bound preservation.
4. Mosco convergence of numerous finite-element convex constraint sets.
5. Vector-valued finite-element convex-hull principles in special low-order
   settings.
6. Strongly monotone/Falk-type variational-inequality transfer arguments.

### D2. Closest collision

Kirby–Shapero’s high-order bounds-satisfying FEM analysis proves approximation
results for the full pointwise bounds-constrained polynomial family. It
explicitly notes that these results do not guarantee high accuracy for the
smaller practical subset obtained by imposing bounds on Bernstein
coefficients.

Allen–Kirby analyze optimization over Bernstein coefficient-constrained
polynomial sets and their multivariate simplex extension. Their results make
the coefficient-cone optimization itself clear prior art.

Hintermüller–Rautenberg–Rösel provide broad density and Mosco-convergence theory
for finite-element convex constraints. Their work means the grand theorem must
be positioned as a specific high-order Bernstein-inner-cone realization, not as
the invention of convex-target Mosco convergence.

### D3. Defensible candidate novelty

Subject to a full expert search, the strongest claim is:

> For fixed-degree conforming simplicial Bernstein finite elements, the
> practical coefficientwise inner constraint admits a constructive high-order
> Mosco recovery; near a regular active interface, globally assembled
> coefficient projection obeys an explicit defect-order/codimension law, which
> combines with multiplier consistency to produce the balanced three-halves
> obstacle rate and its general defect–geometry–duality exponent.

The Lean contribution should be stated separately:

> A machine-checked finite Bernstein certificate and abstract Mosco/VI/rate
> bridge, with the physical Sobolev and free-boundary inputs exposed as
> hypotheses.

### D4. Novelty verdict

**NARROW PASS, confidence 0.60.** No searched source was found containing the
entire coefficient-inner-cone recovery plus the stated free-boundary rate law.
This is not proof of novelty, and the 2017 convex-intersection paper materially
narrows the claim.

---

## Panel E — computational evidence

The deterministic reproduction verifies the encoded coefficient, KKT,
geometry, force-balance and cross-framework tolerances. A separate scikit-fem
assembly is valuable implementation diversity.

**PASS AS COMPUTATIONAL EVIDENCE.** It is not a third-party reproduction because
it remains produced and run inside the same research project. A genuine
clean-room reproduction requires an external group to reconstruct the method
from the paper or frozen protocol.

---

## Required manuscript corrections

1. Replace broad novelty language about convex-target Mosco convergence with the
   narrower Bernstein coefficient-inner-cone claim.
2. Cite Hintermüller–Rautenberg–Rösel prominently in the density/Mosco section.
3. State `r >= 1`, shape regularity, conformity and physical sampling estimates
   in the theorem rather than in proof prose.
4. State the exact cutoff/mollification schedule or cite a density theorem that
   covers closed convex targets containing zero.
5. Separate multiplier-density, measure-multiplier and boundary-multiplier
   variants.
6. Restrict sharpness wording to the phase-locked clipping correction family.
7. Keep the physical theorem labeled “complete under explicit analytical
   hypotheses” until external review and full physical formalization exist.

## Final panel score

- Mathematical architecture under explicit hypotheses: **8.8/10**
- Formal abstract/finite coverage after a successful exact-head audit: **8.5/10**
- Current external validation: **4.0/10**
- Novelty confidence for the narrow combined claim: **6.0/10**
- Readiness for expert circulation after CI and manuscript corrections:
  **7.5/10**

## Principal references checked

- L. Allen and R. C. Kirby, *Bounds-constrained polynomial approximation using
  the Bernstein basis*, Numerische Mathematik 152 (2022), 101–126,
  DOI 10.1007/s00211-022-01311-1.
- R. C. Kirby and D. Shapero, *High-order bounds-satisfying approximation of
  partial differential equations via finite element variational inequalities*,
  arXiv:2311.05880, current indexed revision dated 2026-03-22.
- M. Hintermüller, C. N. Rautenberg and S. Rösel, *Density of convex
  intersections and applications*, Proc. R. Soc. A 473 (2017), 20160919,
  DOI 10.1098/rspa.2016.0919.
- J.-L. Menaldi and C. N. Rautenberg, *On Some Quasi-Variational Inequalities
  and Other Problems with Moving Sets*, arXiv:2106.13665.
- L. Diening, C. Kreuzer and S. Schwarzacher, *Convex Hull Property and Maximum
  Principle for Finite Element Minimisers of General Convex Functionals*,
  arXiv:1302.0112.
