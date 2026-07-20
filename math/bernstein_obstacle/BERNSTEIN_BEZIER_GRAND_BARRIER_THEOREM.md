# The Bernstein–Bézier Grand Barrier Theorem family

Date: 2026-07-20

Status: **canonical research theorem statement**

Formal branch: `formal/bernstein-bezier-grand-canonical`

This document consolidates the strongest defensible theorem family. It separates
complete formal endgames from analytical hypotheses that still require
independent verification or deeper Lean infrastructure.

---

## 1. Bézier Inner-Cone Certificate

Let `T` be a simplex and let

\[
p(x)=\sum_{|\alpha|=r}c_\alpha B_{T,\alpha}(x).
\]

Because the Bernstein basis is nonnegative and forms a partition of unity,

\[
a\le c_\alpha\le b\quad\forall\alpha
\quad\Longrightarrow\quad
 a\le p(x)\le b\quad\forall x\in T.
\]

For spatially varying lower and upper barriers `psi <= phi`, normalize a scalar
Bernstein field `theta_h` by

\[
v_h(x)=\psi(x)+(\phi(x)-\psi(x))\theta_h(x).
\]

If every complete element coefficient of `theta_h` lies in `[0,1]`, then

\[
\psi(x)\le v_h(x)\le\phi(x)
\]

at every physical point of the complete element.

This includes nonpolynomial physical obstacles because only the normalized field
must be polynomial.

Lean endpoints:

- `affineBox_mem_Icc`;
- `boxApprox_mem_Icc`;
- `simplexBoxApproxNat_mem_Icc`.

---

## 2. Bernstein–Bézier Barrier Envelope Theorem

Let

\[
X=W_0^{1,p}(\Omega),\qquad 1<p<\infty,
\]

and

\[
K_{\psi,\phi}
 =\{v\in X:\psi\le v\le\phi\text{ a.e.}\}.
\]

Assume:

1. `Omega` is a bounded polyhedral Lipschitz domain;
2. `psi,phi` have enough smoothness for a uniform second-order positive-sampling
   estimate;
3. `phi-psi >= delta > 0`;
4. the homogeneous trace lies strictly between the barriers in a boundary
   collar;
5. fixed-degree conforming simplicial spaces are uniformly shape regular;
6. strict smooth feasible functions are dense in `K_{psi,phi}` in `W^{1,p}`.

Let `B_h^r` be the positive Bernstein sampling operator and choose constants
`E_psi,E_phi` for the uniform `L-infinity` sampling errors. Define

\[
\psi_h^+=B_h^r\psi+E_\psi h^2,
\qquad
\phi_h^-=B_h^r\phi-E_\phi h^2.
\]

Define the computable coefficient set

\[
K_h^B=\left\{v_h:
 b_{T,\alpha}(v_h-\psi_h^+)\ge0,
 \quad
 b_{T,\alpha}(\phi_h^--v_h)\ge0
 \right\}.
\]

Then, for sufficiently small `h`,

\[
K_h^B\subset K_{\psi,\phi}
\]

with exact whole-element feasibility, and the candidate physical theorem is

\[
K_h^B\xrightarrow{M}K_{\psi,\phi}
\qquad\text{in }W_0^{1,p}(\Omega).
\]

### Recovery mechanism

For a feasible `v`:

1. mix `v` with a fixed strict interior feasible function;
2. approximate in `W_0^{1,p}` by smooth compactly supported functions;
3. retract pointwise into a smaller variable interval;
4. mollify at a scale preserving a positive margin;
5. apply positive Bernstein sampling;
6. choose a diagonal mesh/smoothing schedule so the strict margin dominates the
   conservative `O(h^2)` envelope shifts.

### Formal status

Lean proves the exact implication

> inner inclusion + weak sequential closedness + strong recovery => Mosco
> convergence.

Lean endpoint:

- `BilateralBarrierEnvelopeData.moscoConverges`.

The concrete strict density and physical sampling estimates remain analytical.

---

## 3. Bernstein–Bézier Grand Barrier Theorem

In a real Hilbert space, suppose the continuous and discrete obstacle problems
are projection-form variational inequalities over `K` and `K_h`, with

\[
K_h\subset K.
\]

If the Barrier Envelope hypotheses provide a strongly convergent feasible
recovery sequence, then

\[
K_h\xrightarrow{M}K
\]

and the discrete variational-inequality solutions converge strongly to the
continuous solution.

The proof is the coordinate-free Pythagorean inequality

\[
\|v-u\|^2+\|u-z\|^2\le\|v-z\|^2,
\]

combined for the continuous solution, the discrete solution and a discrete
recovery point.

Lean endpoints:

- `hilbert_vi_pythagorean`;
- `nested_hilbert_vi_recovery_error_sq`;
- `nested_hilbert_vi_strongConvergence_of_recovery`;
- `BilateralBarrierEnvelopeData.grandBarrier_mosco_and_hilbertConvergence`;
- `SobolevFEMRecoveryData.grandBarrier_hilbertConvergence`.

---

## 4. Bernstein–Bézier Inner-Cone Falk Theorem

Let `K_h subset K` be certified inner feasible sets in a Hilbert space. Let `F`
be strongly monotone with constant `alpha>0` and Lipschitz with constant `L`.
Let `u` and `u_h` solve the continuous and discrete variational inequalities.
For every certified recovery `v_h in K_h`, the operator argument yields

\[
\alpha\|u_h-u\|^2
\le
L\|u_h-u\|\,\|v_h-u\|
+\langle F(u),v_h-u\rangle.
\]

Young's inequality gives

\[
\boxed{
\|u_h-u\|^2
\le
\frac{L^2}{\alpha^2}\|v_h-u\|^2
+
\frac{2}{\alpha}\langle F(u),v_h-u\rangle.
}
\]

This endgame does not require symmetry, linearity or an energy functional.

Lean endpoint for the scalar algebra:

- `monotoneInnerCone_falk_sq`.

The derivation from a concrete nonlinear operator is still an analytical/formal
instance to be added.

---

## 5. Topology-free universal branch

For an exact shifted gap with uniformly continuous gradient modulus `omega`,
positive Bernstein recovery gives a topology-independent approximation scale.
With a finite nonnegative contact multiplier, the expected abstract estimate is

\[
\|u-u_h\|_{H^1}
\lesssim
\omega(h)
+
\sqrt{h\,\omega(h)\,\lambda(\Omega)}.
\]

Consequences include:

- `C^{1,beta}` gaps: a corresponding Hölder-modulus rate;
- `C^{1,1}` gaps: a universal first-order branch;
- no regular free-boundary topology is required for this coarse branch.

This branch is weaker than the high-order regular-interface theorem but applies
under substantially weaker geometric assumptions.

Lean endpoints for its coercive algebra:

- `twoScaleRate_of_energy_components`;
- `universalFirstOrderRate_of_energy`;
- `universalFirstOrderRate_of_recovery_and_measure`.

The physical gradient-modulus and Radon-measure estimates remain analytical.

---

## 6. Bernstein–Bézier Codimension–Growth Clipping Law

Suppose a globally conforming coefficient correction `d_h` satisfies:

\[
|c_i(d_h)|\lesssim h_\Gamma^\beta
\]

and is supported on a locally quasi-uniform patch with

\[
|\omega_h|\lesssim h_\Gamma^\kappa.
\]

Reference-element norm equivalence and affine scaling predict

\[
\|d_h\|_{L^q}
\lesssim h_\Gamma^{\beta+\kappa/q},
\]

\[
\|\nabla d_h\|_{L^q}
\lesssim h_\Gamma^{\beta-1+\kappa/q}.
\]

Thus the repair exponent is

\[
\rho_{\rm repair}(q,\beta,\kappa)
=
\beta-1+\frac{\kappa}{q}.
\]

Lean formalizes the exponent algebra. The general `W^{1,q}` patch estimate is a
remaining analytical/formal target; its quadratic `H^1` specialization is
already present in the inherited strip-scaling stack.

---

## 7. Bernstein–Bézier Bregman Transfer Theorem

Assume an energy has two-sided Bregman `q`-growth in the relevant error metric:

\[
c\|v-u\|^q
\le D_J(v,u)
\le C\|v-u\|^q.
\]

Assume a feasible recovery with repair scale

\[
\|v_h-u\|
\lesssim h^r+h_\Gamma^{\beta-1+\kappa/q}
\]

and multiplier consistency

\[
0\le\langle\lambda,v_h-u\rangle
\lesssim h_\Gamma^{\beta+\kappa}.
\]

Then discrete minimality gives

\[
\boxed{
\|u-u_h\|
\lesssim
h^r+h_\Gamma^{\rho(q,\beta,\kappa)},
}
\]

where

\[
\rho(q,\beta,\kappa)
=
\min\left\{
\beta-1+\frac{\kappa}{q},
\frac{\beta+\kappa}{q}
\right\}.
\]

The general real-power/Bregman theorem is analytical only. Lean currently
formalizes the quadratic transfer and the exponent identities.

---

## 8. Three-Halves Contact Law

For quadratic contact on a codimension-one patch in a quadratic energy,

\[
q=2,\qquad\beta=2,\qquad\kappa=1.
\]

Both mechanisms give

\[
\rho_{\rm repair}=\frac32,
\qquad
\rho_{\rm multiplier}=\frac32.
\]

Hence

\[
\boxed{
\|u-u_h^B\|_{H^1}
\lesssim h^r+h_\Gamma^{3/2}.
}
\]

Lean endpoint:

- `threeHalvesContactLaw`.

The inherited v3 stack separately formalizes the corrected quadratic theorem
from explicit bulk, localization, boundary and multiplier assumptions.

---

## 9. Balanced Contact Exponent Principle

The repair and multiplier mechanisms balance when

\[
\beta-1+\frac{\kappa}{q}
=
\frac{\beta+\kappa}{q}.
\]

The patch exponent cancels, leaving

\[
\boxed{
\beta_*(q)=\frac{q}{q-1}.
}
\]

Thus quadratic contact is the balanced order for a quadratic energy.

Lean endpoints:

- `balancedContactOrder`;
- `balancedContactOrder_equalizes`;
- `balancedContactOrder_two`.

---

## 10. Minkowski-codimension extension

A stronger geometric program replaces the integer patch exponent with a
Minkowski-codimension law for the active interface. This predicts repair and VI
rates from:

- coefficient consistency order;
- gap vanishing order;
- interface Minkowski codimension;
- energy exponent.

The phase-locked one-dimensional quadratic model produces an exact
`h^(3/2)` clipping correction, indicating that the three-halves exponent is
sharp for that unfitted family.

This extension currently has analytical and symbolic-computation evidence but
is not part of the canonical Lean endpoint.

---

## 11. What the theorem does not yet cover

The present package does not establish, without additional hypotheses:

- singular or degenerate active interfaces;
- arbitrary measure-valued multipliers in the sharp branch;
- curved changing-normal Signorini contact without a stable lifting theorem;
- frictional contact;
- anisotropic patches;
- merely monotone, non-strongly-monotone operators;
- operator-specific sharp p-Laplacian contact growth;
- optimal adaptive complexity;
- a complete physical `W_0^{1,p}` Lean implementation.

---

## 12. Canonical trust statement

The formal kernel currently certifies the finite Bernstein basis, exact
coefficient feasibility, assembly/conformity, abstract Mosco infrastructure,
Hilbert VI endgame, quadratic rate algebra, and the new canonical composition
lemmas once the canonical integration audit succeeds.

The strict physical recovery construction, general `W^{1,p}` sampling,
free-boundary geometry, general Bregman theory and nonlinear operator instances
remain analytical obligations. Independent mathematical and prior-art review is
required before the theorem family is advertised as a new established theorem.
