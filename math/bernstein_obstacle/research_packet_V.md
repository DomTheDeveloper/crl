# Pointwise-Feasible Bernstein–Bézier Obstacle Variational Inequalities

## Research Packet V — saved July 20, 2026

## Executive status

This packet consolidates the project after completing the three highest-value
research approaches:

1. a pointwise a posteriori barrier theorem in one dimension;
2. nested conforming local refinement with coefficient-preserving Bernstein
   subdivision;
3. a physical membrane-contact benchmark with dual contact-pressure
   reconstruction and a mixed-style baseline.

The strongest paper-level claim remains the regular-free-boundary estimate

\[
\|u-u_h^B\|_{H^1(\Omega)}
\le C\left(h^r+h_\Gamma^{3/2}\right),
\]

under explicit assumptions on free-boundary regularity, quadratic growth,
multiplier boundedness, obstacle representation, and mesh grading.

That multidimensional theorem is a strong proof candidate rather than a final
peer-audited theorem. The new one-dimensional Green-barrier theorem and the
Bernstein subdivision identities are complete under their stated hypotheses.

---

# 1. Continuous obstacle problem

Let \(\Omega\subset\mathbb R^d\) be bounded and Lipschitz and let

\[
K=\{v\in H_g^1(\Omega):v\ge\psi\text{ a.e.}\}.
\]

For a symmetric continuous coercive form \(a\) and load functional \(F\), the
solution satisfies

\[
u\in K,
\qquad
a(u,v-u)\ge F(v-u)\quad(v\in K).
\]

For the classical membrane operator,

\[
-\Delta u-f=\lambda,
\qquad
u-\psi\ge0,
\qquad
\lambda\ge0,
\qquad
\lambda(u-\psi)=0.
\]

Write

\[
w=u-\psi,
\qquad
\Omega^+=\{w>0\},
\qquad
\Lambda=\{w=0\},
\qquad
\Gamma=\partial\Omega^+\cap\Omega.
\]

---

# 2. Bernstein–Bézier feasible cone

On a simplicial mesh \(\mathcal T_h\), let \(V_h^r\) be a conforming
polynomial space of degree \(r\). On each element,

\[
q_h|_T=\sum_{|\alpha|=r}b_{T,\alpha}(q_h)B^T_\alpha.
\]

Define

\[
K_h^B=
\left\{
v_h\in V_h^r:
 b_{T,\alpha}(v_h-\psi_h)\ge0
 \text{ for every }T,\alpha
\right\}.
\]

Since the Bernstein basis is nonnegative and forms a partition of unity,

\[
K_h^B\subseteq
\{v_h\in V_h^r:v_h\ge\psi_h\text{ pointwise}\}.
\]

This is the project’s central computational property: feasibility is certified
throughout each element, not merely at nodes or quadrature points.

---

# 3. Completed one-dimensional Mosco theorem

On \(I=[0,1]\), let \(1<p<\infty\) and let \(v,\psi\in W^{1,p}(I)\) satisfy
\(v\ge\psi\). Define

\[
B_n f(x)=\sum_{k=0}^nf(k/n)\binom nkx^k(1-x)^{n-k}.
\]

Set \(v_n=B_nv\) and \(\psi_n=B_n\psi\). Then

\[
v_n-\psi_n=B_n(v-\psi),
\]

whose \(k\)-th coefficient is \((v-\psi)(k/n)\ge0\). Moreover,

\[
v_n\to v\quad\text{in }W^{1,p}(I).
\]

Endpoint values are preserved. The recovery condition follows immediately.
The weak-limit condition follows from the compact embedding
\(W^{1,p}(I)\hookrightarrow C([0,1])\). Hence the global one-dimensional
Bernstein cones Mosco-converge to the continuous obstacle cone.

---

# 4. Regular-free-boundary coefficient repair

## 4.1 Assumptions

For the cleanest theorem, assume:

1. the obstacle is zero or represented exactly;
2. \(\Gamma\Subset\Omega\) is a compact \(C^1\) hypersurface;
3. \(w\in C^{1,1}(\Omega)\) and is piecewise
   \(W^{r+1,\infty}\) away from \(\Gamma\);
4. \(w=\nabla w=0\) on \(\Gamma\);
5. on the positive side near \(\Gamma\),
   \[
   c_0d(x,\Gamma)^2\le w(x)\le C_0d(x,\Gamma)^2;
   \]
6. the mesh is shape regular and locally quasi-uniform in a tubular
   neighborhood of \(\Gamma\), with local diameter \(h_\Gamma\);
7. the multiplier belongs to \(L^\infty(\Omega)\).

## 4.2 Coefficient-to-grid-value lemma

For an affine-reproducing stable local interpolation operator \(I_T^r\),

\[
\left|
b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})
\right|
\le
C_rh_T^2|v|_{W^{2,\infty}(T)}.
\]

The functional

\[
L_{T,\alpha}(v)=b_{T,\alpha}(I_T^rv)-v(x_{T,\alpha})
\]

annihilates \(\mathbb P_1\). Mapping to the reference simplex and applying
Bramble–Hilbert yields the estimate.

## 4.3 Localization

If

\[
\operatorname{dist}(T,\Gamma)\ge\kappa h_T,
\]

then quadratic nondegeneracy gives

\[
w(x_{T,\alpha})\ge c_0(\kappa-1)^2h_T^2.
\]

For sufficiently large fixed \(\kappa\), this dominates the coefficient error,
so every coefficient is nonnegative. Coefficient violations are therefore
confined to an \(O(h_\Gamma)\)-thick strip around \(\Gamma\).

Inside that strip,

\[
b_{T,\alpha}(I_h^rw)\ge-Ch_\Gamma^2.
\]

## 4.4 Positive repair

Let \(\eta_h\) be a continuous nonnegative piecewise-linear cutoff satisfying

- \(\eta_h=1\) on every risky element;
- \(0\le\eta_h\le1\);
- its support lies in a one-ring enlargement of the strip;
- \(\|\nabla\eta_h\|_\infty\le Ch_\Gamma^{-1}\).

Set

\[
w_h^B=I_h^rw+C_*h_\Gamma^2\eta_h.
\]

The degree-elevated Bernstein coefficients of \(\eta_h\) are nonnegative, so
\(w_h^B\) is coefficient-feasible. Since the support has measure
\(O(h_\Gamma)\),

\[
\|h_\Gamma^2\eta_h\|_{L^2}=O(h_\Gamma^{5/2}),
\qquad
\|\nabla(h_\Gamma^2\eta_h)\|_{L^2}=O(h_\Gamma^{3/2}).
\]

Combining strip and bulk interpolation estimates gives the candidate recovery
result

\[
\boxed{
\|w-w_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
}
\]

## 4.5 Falk step

For any feasible recovery \(v_h^B\), the exact-obstacle Falk estimate has the
form

\[
c\|u-u_h^B\|_{H^1}^2
\lesssim
\|u-v_h^B\|_{H^1}^2
+
\langle\lambda,v_h^B-u\rangle.
\]

On the contact portion of the risky strip, the recovery lift has amplitude
\(O(h_\Gamma^2)\) over a set of measure \(O(h_\Gamma)\). Thus

\[
\langle\lambda,v_h^B-u\rangle
\le C\|\lambda\|_\infty h_\Gamma^3.
\]

Taking square roots yields

\[
\boxed{
\|u-u_h^B\|_{H^1}
\le C(h^r+h_\Gamma^{3/2}).
}
\]

The remaining publication audit must spell out the interpolation operator,
cutoff construction, transition-mesh assumptions, approximate-obstacle term,
and treatment of singular or boundary-touching free boundaries.

---

# 5. Completed one-dimensional pointwise barrier theorem

This is the main new theorem in Packet V.

Let \(u\) solve the one-dimensional obstacle problem with obstacle zero and
fixed endpoint values. Let \(v\) be any feasible continuous piecewise-\(C^2\)
function with the same boundary values. Define the signed residual measure

\[
q=-D^2v-f\,dx.
\]

For a piecewise-smooth \(v\), this measure contains both cell residuals and
node masses:

\[
q|_T=(-v''-f)\,dx,
\qquad
q(\{x_i\})=-[v']_{x_i}.
\]

Let \(q=q^+-q^-\) be its Jordan decomposition and let \(G\) be the positive
Dirichlet Green operator for \(-d^2/dx^2\).

## Upper barrier

Set

\[
z^+=Gq^-.
\]

Then \(z^+\ge0\), vanishes at the endpoints, and

\[
-D^2(v+z^+)-f=q^+\ge0.
\]

Thus \(\overline v=v+z^+\) is a feasible supersolution and

\[
u\le\overline v.
\]

## Lower barrier

Let \(q^+_{\{v>0\}}\) be the restriction of the positive residual to the set
where \(v\) is strictly above the obstacle. Set

\[
z^-=Gq^+_{\{v>0\}},
\qquad
\underline v=(v-z^-)^+.
\]

On \(\{\underline v>0\}\), one has \(v>0\), and

\[
-D^2(v-z^-)-f\le0.
\]

The rectification contributes only a favorable measure at zero crossings.
Therefore \(\underline v\) is a subsolution and

\[
\underline v\le u.
\]

## Reliable enclosure

Consequently,

\[
\boxed{
(v-z^-)^+\le u\le v+z^+,
}
\]

and

\[
\boxed{
\|u-v\|_{L^\infty}
\le
\max(\|z^+\|_{L^\infty},\|z^-\|_{L^\infty}).
}
\]

This proves pointwise reliability. The current quadrature implementation
verified the enclosure in every manufactured test, but was highly
inefficient: effectivity indices ranged from roughly 23 to above 10,000.
The cause is the nonlocal splitting of large, canceling residual and jump
measures. A multidimensional and efficient theorem should use the more subtle
barrier rectification and quasi-discrete contact-force ideas from recent
Signorini analysis.

---

# 6. Nested conforming edge-bisection and Bernstein subdivision

The previous adaptive prototype inserted centroids and rebuilt a global
Delaunay triangulation. That improved errors quickly but was not nested and
could perturb resolved regions.

Packet V implements nested local edge bisection:

1. each marked triangle requests its longest edge;
2. a shared edge receives one globally shared midpoint;
3. every incident triangle uses that midpoint;
4. local one-, two-, and three-edge split patterns are triangulated inside the
   parent;
5. all old vertices and all parent element domains are retained.

The resulting mesh is conforming and nested.

## 6.1 Exact child restriction

For a child triangle with vertices \(w_0,w_1,w_2\) expressed in parent
barycentric coordinates, let \(R_c\) be the matrix satisfying

\[
\mathbf b_c=R_c\mathbf b_T.
\]

The implemented matrix is obtained by evaluating the parent polynomial at the
child barycentric grid and converting those values into child Bernstein
coefficients. This is algebraically equivalent to affine de Casteljau
subdivision.

Tests across degrees three and four gave:

- polynomial reproduction errors between \(1.7\times10^{-16}\) and
  \(4.4\times10^{-16}\);
- discrepancies at shared prolonged degrees of freedom between
  \(1.1\times10^{-16}\) and \(4.4\times10^{-16}\);
- minimum restriction-matrix entries no smaller than about
  \(-5.9\times10^{-16}\), i.e. nonnegative up to floating-point roundoff;
- prolonged minimum coefficients no smaller than about
  \(-2.7\times10^{-16}\).

Thus subdivision preserves the represented function, conformity, and
coefficient positivity to machine precision.

## 6.2 Adaptive results

### Degree three

\[
\begin{array}{c|c|c}
\text{unknowns}&H^1\text{ error}&L^2\text{ error}\\\hline
289&0.276761&0.008618\\
442&0.239284&0.005959\\
955&0.220337&0.005420\\
1414&0.127918&0.004474\\
3628&0.119598&0.004405
\end{array}
\]

### Degree four

\[
\begin{array}{c|c|c}
\text{unknowns}&H^1\text{ error}&L^2\text{ error}\\\hline
529&0.187173&0.010185\\
801&0.101596&0.004338\\
1761&0.095800&0.004120\\
3609&0.062272&0.002157\\
6687&0.057006&0.001858
\end{array}
\]

The nested method converges more steadily than centroid remeshing, but its
current longest-edge marking is less aggressive and initially less accurate
per degree of freedom. The correct production method should combine:

- nested newest-vertex or compatible edge bisection;
- Dörfler residual/interface marking;
- coefficient-preserving prolongation as implemented here;
- PDAS warm starts using the prolonged coefficient and multiplier vectors.

---

# 7. Physical membrane contact and multiplier comparison

Consider a membrane on \([0,1]\) above the flat obstacle \(0\), subject to
constant load \(f=-1\). Select \(a=0.32\), \(b=0.68\), and endpoint values

\[
u(0)=\frac{a^2}{2},
\qquad
u(1)=\frac{(1-b)^2}{2}.
\]

The exact solution is

\[
u(x)=
\begin{cases}
\frac12(a-x)^2,&x<a,\\
0,&a\le x\le b,\\
\frac12(x-b)^2,&x>b,
\end{cases}
\]

with exact pressure

\[
\lambda(x)=\mathbf1_{[a,b]}(x).
\]

The exact total contact force is

\[
\int_0^1\lambda\,dx=b-a=0.36.
\]

## 7.1 Bernstein method

For degrees two through four and 12, 24, and 48 elements:

- every run had zero sampled obstacle penetration;
- KKT residuals were between \(10^{-16}\) and \(10^{-15}\);
- total reconstructed contact force was between \(0.359878\) and \(0.361242\);
- the best displacement errors were
  \[
  \|u-u_h\|_{L^2}\approx10^{-6},
  \qquad
  |u-u_h|_{H^1}\approx1.57\times10^{-4};
  \]
- the best pressure \(L^1\) error was approximately \(0.0167\).

The coefficient-dual force was reconstructed as an \(L^2\) function through
the finite-element mass matrix. It recovers total force very accurately but
still exhibits local pressure oscillation near contact transitions.

## 7.2 Cell-average mixed-style baseline

A standard piecewise-linear displacement was constrained only through cell
averages. Its cell duals were interpreted as piecewise-constant pressure.

At 96 elements:

\[
\|u-u_h\|_{L^2}\approx6\times10^{-6},
\qquad
|u-u_h|_{H^1}\approx2.41\times10^{-3},
\]

with total force \(0.359971\). However, the solution dipped slightly below the
obstacle between enforcement points. The violation decreased from about
\(3.4\times10^{-5}\) at 24 elements to \(4.4\times10^{-7}\) at 96 elements.

This benchmark demonstrates the core distinction:

- average/nodal constraints can approximate contact well but permit small
  between-constraint penetration;
- Bernstein coefficient constraints guarantee continuous pointwise
  nonpenetration.

---

# 8. Constraint-cone hierarchy

For dyadic Bernstein subdivisions \(\mathcal S_\ell(T)\), define

\[
\mathcal C_\ell(T)=
\{p\in\mathbb P_r(T):
\text{all Bernstein coefficients of }p|_S
\text{ are nonnegative for every }S\in\mathcal S_\ell(T)\}.
\]

Then

\[
\mathcal C_0(T)\subseteq
\mathcal C_1(T)\subseteq
\cdots\subseteq
\{p:p\ge0\text{ on }T\}.
\]

Subdivision coefficients are convex combinations of parent coefficients, so
nesting and feasibility are exact. If \(p\ge\delta>0\), sufficiently fine
subdivision places \(p\) in \(\mathcal C_\ell\). Thus the cones approximate
the strictly positive polynomial cone from inside.

In the coarse two-dimensional degree-four test, one subdivision reduced the
\(H^1\) error by approximately 11.4% relative to raw coefficient constraints
while retaining certified positivity. GLL-node constraints satisfied all
nodes yet dipped below the obstacle between nodes.

---

# 9. Adjacent 2026 research and implications

## hp/spectral obstacle methods

A June 2026 hp/spectral method proves convergence of GLL-constrained obstacle
sets and an \(O(h/N)\) error estimate, with hp-adaptive dam-seepage tests. It
is the closest direct competitor. The Bernstein paper must focus on global
pointwise feasibility, coefficient-cone approximation, repair, and
subdivision—not merely high-order obstacle FEM.

## Proximal DG and proximal Galerkin

Current proximal DG/HHO work gives unified primal and dual error estimates and
higher-order convergence. Prox-based semismooth Newton theory gives local
superlinear convergence for obstacle and related convex problems. These are
solver and analysis baselines, not gaps the Bernstein paper should claim.

## Supremum-norm Signorini barriers

A June 2026 adaptive Signorini method proves reliability and efficiency using
upper/lower barriers formed by rectifying the discrete solution. This is the
strongest tool for extending the one-dimensional Green-barrier theorem to
multiple dimensions.

## Mixed multipliers

Recent mixed beam-obstacle methods provide stable dual spaces, a priori and a
posteriori estimates, and PDAS/Uzawa algorithms. The Bernstein KKT pressure
should be compared against these multiplier spaces, including pressure norms
and total contact force.

## Certified polynomial range bounds

Recent high-order range-bounding work produces tighter subcell extrema than
traditional Bernstein convex hulls. A strong future comparison is

\[
K_h^{B}
\subseteq
K_h^{\mathrm{subdivided\ B}}
\subseteq
K_h^{\mathrm{range}}
\subseteq
K_h^{\mathrm{pointwise}}.
\]

## Adaptive isogeometric and multiscale contact

Current adaptive NURBS contact and high-contrast multiscale contact methods
refine or update bases only in active contact regions. They motivate local
basis enrichment and a Hertzian or large-deformation benchmark after the
first obstacle paper.

---

# 10. Reproducible artifacts

The packet contains:

- `adaptive_triangular_bernstein.py`
- `adaptive_hybrid_bernstein.py`
- `nested_bernstein_refinement.py`
- `constraint_cone_benchmark.py`
- `pointwise_barrier_contact_benchmark.py`
- all primary CSV result tables;
- all generated benchmark plots;
- literature matrices and earlier research packets.

Every script uses deterministic inputs and reports KKT residuals, minimum
sampled solution values, and approximation errors.

---

# 11. Honest readiness assessment

| Component | Status |
|---|---:|
| Exact global coefficient feasibility | 100% |
| One-dimensional Mosco theorem | 100% |
| One-dimensional pointwise barrier theorem | 95% |
| Numerical barrier implementation | 75% reliability / low efficiency |
| Regular-free-boundary repair proof | 92% under restricted assumptions |
| Falk minimizer estimate | 88% under restricted assumptions |
| Subdivision-cone theorem | 98% |
| Hybrid adaptive solver | 90% prototype |
| Nested conforming refinement | 90% prototype |
| Coefficient-preserving prolongation | 98% numerical verification |
| Physical contact benchmark | 88% |
| Multiplier reconstruction | 75% |
| Mixed multiplier comparison | 55% |
| Multidimensional pointwise estimator | 35% |
| Manuscript | 60% |
| Independent proof/code audit | 12% |

## What remains before a 10/10 submission

1. turn the regular-free-boundary proof into a line-by-line publication proof;
2. replace local Delaunay templates with a formally specified NVB or red-green
   refinement family and prove closure complexity;
3. use prolonged primal and dual vectors as PDAS warm starts;
4. prove or carefully delimit multidimensional pointwise reliability;
5. implement a stable mixed multiplier baseline in two dimensions;
6. add a physically recognizable indentation, Signorini, or elastic–rigid
   benchmark;
7. run independent mathematical and software audits;
8. write the final manuscript and reproducibility appendix.
