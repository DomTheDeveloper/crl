# Adversarial audit of the Grand Positive-Basis Constraint Theorem

## Verdict

**PASS AFTER CORRECTION for the mathematical architecture.**

**Novelty remains UNCONFIRMED pending independent expert review.**

The unilateral universal-rate argument, nonsymmetric Falk transfer, Minkowski
repair scaling, quadratic-contact clipping example, and bilateral normalization
are internally coherent under the corrected hypotheses below.  The package must
not be described as fully Lean-formalized or independently established: the
concrete Sobolev estimates, Radon-measure representation in a given PDE, and full
function-space unilateral/bilateral theorems remain analytical.

---

## Required corrections to the theorem statement

1. **Measure pairing.**  If the multiplier belongs to `H^{-1}` and extends to a
   finite Radon measure, its action on Sobolev functions is understood through
   quasi-continuous representatives.  In this theorem the recovery difference is
   continuous, so the dual pairing agrees with the Radon integral.  This must be
   stated explicitly.

2. **Interior contact only.**  The identity `grad g(x)=0` is used only for
   `x in Omega`.  The closure of the contact set may reach the physical boundary,
   but no boundary-supported multiplier is included.

3. **Fixed-degree affine simplices.**  The positive sampling proof assumes a
   fixed polynomial degree on both sides of every face and affine, shape-regular
   simplices.  Curved/isoparametric elements, variable degree across a face, and
   anisotropic degeneracy require separate analysis.

4. **Exact integration for nonpolynomial shifts.**  `psi + V_h` and
   `psi + (phi-psi)V_h` are legitimate finite-dimensional affine trial sets, but
   they are not ordinary polynomial finite-element spaces when the obstacles are
   nonpolynomial.  The stated theorem is for the exact variational forms; any
   quadrature error needs a Strang-type perturbation analysis.

5. **Nonsymmetric terminology.**  For a nonsymmetric coercive bilinear form the
   result concerns the unique variational-inequality solution, not an energy
   minimizer.

6. **Minkowski theorem is conditional.**  The exponent law assumes, rather than
   proves for a PDE, localization of all negative coefficients, repair amplitude
   `O(h^a)`, inverse stability, and a tubular-volume estimate.  The theorem is a
   classification of the consequences of those inputs.

7. **Exponent domain.**  The current Lean Minkowski files formalize integer
   vanishing orders and integer codimensions.  The manuscript's real-valued
   Minkowski exponent `s` and general real vanishing order `q` are analytical
   extensions, not yet kernel-checked.

8. **Sharpness scope.**  The exact `h^(3/2)` construction proves sharpness for the
   stated phase-locked, unfitted, coefficientwise-clipping family.  It is not an
   impossibility theorem for all high-order obstacle methods.

9. **Bilateral boundary data.**  The clean box theorem assumes the normalized
   variable has homogeneous trace, or that an exact normalized boundary lift is
   supplied.

10. **Width regularity.**  The bilateral rate requires
    `w = phi-psi in W^{1,infinity}` and `w >= w0 > 0`; exact box feasibility alone
    does not require this, but the `H1` rate does.

---

## Mathematical audit

### 1. Affine shifted trial set — PASS AFTER CLARIFICATION

For fixed `psi in H^1`, the map `z_h -> psi + z_h` sends the finite-dimensional
space `V_h` to a finite-dimensional affine subset of `H^1`.  Coefficient
nonnegativity of `z_h` gives `psi+z_h >= psi` pointwise.  The formulation is
mathematically legitimate, although exact quadrature is part of the theorem.

### 2. Nonsymmetric existence and uniqueness — PASS

A continuous coercive bilinear form defines a strongly monotone linear operator.
The standard Lions--Stampacchia theorem gives a unique VI solution on each
nonempty closed convex set.  Symmetry is unnecessary for well-posedness.

### 3. Positive recovery and conformity — PASS UNDER FIXED-DEGREE ASSUMPTION

Samples of a nonnegative gap are nonnegative Bernstein coefficients.  The
Bernstein basis is nonnegative and sums to one, giving whole-element feasibility.
Shared-face lattice points are intrinsic to the face, so traces agree when the
same degree is used on adjacent elements.  Zero boundary trace makes all samples
on physical boundary faces vanish.

### 4. Local gradient-modulus estimate — PASS AS AN ANALYTICAL LEMMA

Affine reproduction and fixed-degree reference-element stability imply

`||grad(g-B_T g)||_L2(T) <= C |T|^(1/2) omega_T(h_T)`.

The repository now formalizes the finite consequence: a samplewise segment bound
`g(x_alpha) <= dist(x_alpha,x) omega_T(h_T)` and `dist <= h_T` propagate through
the complete simplex Bernstein basis to

`0 <= B_T g(x) <= h_T omega_T(h_T)`.

The differential/reference-element estimate itself remains analytical.

### 5. Poincare step — PASS

Both the exact gap and assembled positive recovery have homogeneous trace, so
their difference lies in `H_0^1`; the global `L2` term is controlled by the
gradient error.

### 6. Zero gradient at contact — PASS FOR INTERIOR CONTACT

If `g >= 0`, `g(x)=0`, and `g` is differentiable at an interior point, then `x`
is a local minimum and `grad g(x)=0`.  This is not asserted at a physical-boundary
point.

### 7. Mesh-skeleton contact — PASS

At an interior contact point on a face, the estimate is valid on every incident
element.  Defining `q_h` by the maximum over incident closed elements removes
ambiguity if the Radon measure charges an interior face or lower-dimensional
skeleton.

### 8. Radon-measure multiplier — PASS AFTER REPRESENTATIVE CLARIFICATION

A positive multiplier in `H^{-1}` represented by a finite Radon measure is diffuse
with respect to `H^1` capacity.  Pairings are interpreted using quasi-continuous
representatives.  Since the positive Bernstein recovery is continuous, the
contact pairing used in the proof is the ordinary Radon integral.

### 9. Nonsymmetric Falk signs — PASS

Let `e=u-u_h`.  The discrete VI gives

`a(e,v_h-u_h) <= lambda(v_h-u_h)`.

Because `u_h` is continuously feasible,

`lambda(u_h-u) >= 0`,

and therefore

`lambda(v_h-u_h) <= lambda(v_h-u)`.

Combining this with coercivity, continuity, and Young's inequality gives the
claimed transfer without symmetry.

### 10. Universal local/global rates — PASS

The local indicators yield

`||u-u_h||_H1^2 <= C(eta_h^2+mu_h)`.

For a global gradient modulus,

`eta_h <= |Omega|^(1/2) omega(h)`

and

`mu_h <= h omega(h) lambda(Omega)`.

Thus

`||u-u_h||_H1 <= C(omega(h)+sqrt(h omega(h) lambda(Omega)))`.

For `omega(h)=O(h^beta)`, `0<beta<=1`, the second term decays at least as fast as
`h^beta`, giving `O(h^beta)`.

### 11. Boundary-touching active set — PASS WITH NARROW MEANING

The closure of the interior active set may meet `partial Omega`.  The proof does
not cover a multiplier supported on the physical boundary.

### 12. Minkowski repair law — PASS CONDITIONALLY

If repair amplitude is `h^a`, inverse scaling contributes `h^{-1}`, and the risky
patch has volume `delta_h^s` with `delta_h=h^(a/q)`, then

`||d_h||_H1 = O(h^(a-1+sa/(2q)))`.

A bounded-density contact term produces the competing square-root exponent,
giving

`rho_VI = sa/(2q) + min(a-1,a/2)`.

The algebra is correct; proving the geometric/localization assumptions for a PDE
is separate.

### 13. Consistency-limited order — PASS CONDITIONALLY

The choice `a=min(m,q)` correctly records that coefficient accuracy cannot reduce
true gap values on a cut element below the physical vanishing scale.

### 14. Quadratic-contact saturation — PASS WITH RESTRICTED SCOPE

For `q=2`, codimension one, and `m>=2`, the classification gives `rho=3/2`.  The
phase-locked P2 cut-cell calculation supplies an exact lower bound of that order
for coefficientwise clipping.  Earlier quadratic-FEM literature already contains
`h^(3/2-epsilon)` convergence phenomena, so the exponent itself is not new.

### 15. Bilateral normalization — PASS

With `w=phi-psi>=w0>0`, `theta=(u-psi)/w` converts the physical box to `[0,1]`.
Bernstein coefficients in `[0,1]` imply `theta_h in [0,1]` everywhere and hence
`psi<=psi+w theta_h<=phi`, even for nonpolynomial obstacles.

### 16. Bilateral multiplier signs — PASS

Writing the residual as `lambda_- - lambda_+`, the lower contribution is positive
because `v-u>=0` on lower contact; the upper contribution is positive because
`v-u<=0` on upper contact.  Sampling `theta` and `1-theta` gives symmetric
contact estimates.

### 17. Lean faithfulness — PASS FOR THE DECLARED FINITE/ALGEBRAIC LAYER, PENDING CI

The repository contains declarations for positivity, range certificates,
conformity, translated Mosco endgames, moving-obstacle composition, Minkowski
integer-exponent algebra, saturation algebra, affine box certificates, finite
samplewise contact propagation, weighted contact sums, and coercive rate transfer.
The exact PR-head audit must complete successfully before these new declarations
are called kernel-verified.

### 18. Trust boundary — PASS AFTER CORRECTION

The theorem document must continue to label as analytical:

- the fixed-degree Sobolev gradient-modulus estimate;
- PDE-specific measure-multiplier identification;
- the complete unilateral and bilateral function-space theorem;
- real-exponent Minkowski geometry;
- any quadrature/implementation perturbation for nonpolynomial shifts.

---

## Prior-art collision audit

The following components are established prior art and must not be claimed alone:

1. General VI approximation and classical `O(h)` obstacle estimates:
   Falk (1974); Brezzi--Hager--Raviart (1977).
2. Nonsymmetric and hp-adaptive obstacle FEM:
   Banz--Schroeder (2015), plus earlier p-version work.
3. Bounds-constrained polynomial approximation using Bernstein coefficients,
   including simplices:
   Allen--Kirby (2022).
4. High-order bounds-satisfying finite-element variational inequalities and use
   of Bernstein coefficient constraints as a practical sufficient subset:
   Kirby--Shapero (2024).
5. hp/spectral obstacle discretization with GLL constraints, Bernstein positivity,
   convergence, and an `O(h/N)` estimate:
   Bekhouche--Benchettah (2026).
6. Quadratic/high-order obstacle methods exhibiting `3/2` or
   `3/2-epsilon` free-boundary-limited behavior:
   established quadratic FEM literature and later mixed/stabilized studies.
7. Double/two-phase obstacle formulations and box-constrained dual problems:
   existing bilateral and two-phase obstacle literature.

### Candidate contribution that survives this audit

The strongest potentially new contribution is the **specific combined theorem and
proof architecture**, not any one ingredient:

- exact complete-element positive-basis certification;
- a local gradient-modulus/contact-measure estimate for positive sampling without
  regular active-set geometry;
- a conditional Minkowski/vanishing-order classification of clipping repair;
- an exact cut-cell lower bound showing the `3/2` barrier for a defined clipping
  class;
- moving/nonpolynomial affine shifts and bilateral coefficient boxes in the same
  framework;
- a substantial Lean-checked finite and abstract bridge.

A qualified literature reviewer must still decide whether the local
modulus/contact-measure estimate or the Minkowski classification is already
implicit in classical Falk-type analyses.

---

## Bibliographic anchors

- R. S. Falk, *Error estimates for the approximation of a class of variational
  inequalities*, Mathematics of Computation 28 (1974), 963--971.
- F. Brezzi, W. W. Hager, P. A. Raviart, *Error Estimates for the Finite Element
  Solution of Variational Inequalities. Part I. Primal Theory*, Numerische
  Mathematik 28 (1977), 431--444.
- L. Banz, A. Schroeder, *Biorthogonal basis functions in hp-adaptive FEM for
  elliptic obstacle problems*, Computers & Mathematics with Applications 70
  (2015), 1721--1742.
- T. Gustafsson, R. Stenberg, J. Videman, *Mixed and Stabilized Finite Element
  Methods for the Obstacle Problem*, SIAM Journal on Numerical Analysis 55
  (2017), 2718--2744.
- L. Allen, R. C. Kirby, *Bounds-constrained polynomial approximation using the
  Bernstein basis*, Numerische Mathematik 151 (2022), 101--126.
- R. C. Kirby, D. Shapero, *High-order bounds-satisfying approximation of partial
  differential equations via finite element variational inequalities*,
  Numerische Mathematik 156 (2024), 927--947.
- R. O. E. Bekhouche, D. C. Benchettah, *hp-adaptive/Spectral Element Methods for
  Elliptic Obstacle and Free Boundary Problems*, Communications in Nonlinear
  Science and Numerical Simulation, article 110252 (2026).
