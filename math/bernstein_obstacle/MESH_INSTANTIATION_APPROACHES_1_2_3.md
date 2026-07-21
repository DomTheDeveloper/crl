# Concrete mesh instantiation program for the certified Bernstein–Bézier saturation theorem

This note develops three routes from the certified conditional theorem

```text
BernsteinObstacle.bernsteinBezier_quadraticContact_fullSpace_threeHalvesSaturation
```

to concrete mesh/PDE statements.  The first two routes are positive theorem programs.
The third route identifies a sharp obstruction and replaces an impossible universal
claim by a phase-weighted criterion.

## 0. Common PDE model and regular-patch assumptions

Let `Omega` be a planar domain and let `u` solve the classical scalar obstacle
problem with obstacle `psi`.  On a compact regular free-boundary arc `Gamma0`, assume
there are constants

```text
a0 > 0, A0 < infinity, kappa > 0, KR < infinity
```

and a unit normal field `nu` such that, in a tubular neighborhood of `Gamma0`,

```text
u - psi = a(s) (t_+)^2 + R(s,t),
a0 <= a(s) <= A0,
|grad R(s,t)| <= KR |t|^(1+kappa).
```

Here `(s,t)` are arclength/normal coordinates.  For the normalized classical
obstacle equation `Delta(u-psi)=1` in the noncontact region, the regular blow-up is
the half-parabola `1/2 (t_+)^2`; a variable positive coefficient is retained here to
cover normalization and variable-coefficient forms.

The certified Lean theorem already converts these analytic and geometric inputs into
a two-sided `h^(3/2)` estimate.  The remaining job is to verify the inputs for a
concrete mesh family.

---

# Approach 1: deterministic phase-separated meshes

## 1A. Exact flat-interface benchmark

This is the fastest completely explicit theorem and should be proved first.

Take

```text
Omega = (-L,L) x (-H,H),
psi = 0,
u(x,y) = a (y_+)^2,
f = -2a,
a > 0.
```

With Dirichlet data equal to `u` on the boundary, `u` solves the obstacle problem:

```text
u >= 0,
-Delta u - f = 0 on {y>0},
-Delta u - f = 2a >= 0 on {y<=0}.
```

The free boundary is the straight segment `Gamma = {y=0}` and the remainder is
identically zero.

### Mesh family

Use a uniform square grid of side `h`, shifted in the normal direction so that the
rows adjacent to the interface are

```text
y = -h/2 and y = h/2.
```

Split every square by the same southwest-to-northeast diagonal.  The mesh is
quasi-uniform and shape regular, while the free boundary passes through the interior
of the two triangles in each interface square.

Fix `rho = 1/4`.  In each cut square, each of the two cut triangles contains a
rectangle/prism of the form

```text
Y_T x [-rho h, rho h]
```

with

```text
length(Y_T) >= rho h,
phase theta = 1/2,
Jacobian J0 = 1.
```

Thus one may take uniform constants

```text
eta = 1/2,
M = rho,
J0 = 1,
N proportional to length(Gamma).
```

The number of retained triangles is bounded below by `c L / h`.

### Explicit feasible upper comparison

On the interface strip `|y| <= h/2`, define

```text
q_h(y) = (a/4) (y + h/2)^2.
```

Outside the strip set

```text
v_h = 0                    for y <= -h/2,
v_h = a y^2                for y >= h/2.
```

Then `v_h` is continuous, nonnegative, and quadratic on every triangle.  Hence it is
a conforming feasible `P2` finite-element function.  Its derivative error is supported
only in the interface strip and is `O(h)` pointwise, so

```text
|u-v_h|_(H1)^2 <= C a^2 L h^3.
```

The obstacle multiplier term in Falk's inequality is also `O(h^3)`, because the
positive repair on the contact side has height `O(h^2)` over a strip of area `O(Lh)`.
Therefore the discrete obstacle solution satisfies

```text
|u-u_h|_(H1) <= C h^(3/2).
```

The certified full-space lower theorem gives the matching lower bound.  Consequently
this benchmark has a completely explicit sharp estimate

```text
c h^(3/2) <= |u-u_h|_(H1) <= C h^(3/2).
```

### Status of 1A

Human proof architecture: essentially complete.

Remaining work:

1. write the exact Falk-inequality constants;
2. encode the rectangular shifted mesh and the two retained triangle types;
3. feed the explicit prism constants into the certified Lean endpoint.

This is the best first concrete theorem because the PDE expansion is exact and the
remainder is zero.

## 1B. Curved regular arc with a designed tubular mesh

Let `gamma:[0,L]->Omega` parametrize a `C^2` regular free-boundary arc with curvature
bounded by `K`.  In a tubular neighborhood use

```text
F(s,t) = gamma(s) + t nu(s).
```

For `|t| <= r0` with `K r0 < 1`, the Jacobian is

```text
J(s,t) = 1 - t kappa_gamma(s),
J >= 1 - K r0 > 0.
```

Construct vertices at

```text
F(jh, (k+1/2)h)
```

and connect neighboring vertices by straight segments, splitting each quadrilateral
consistently into two triangles.  The free boundary `t=0` lies midway between two
normal rows.

For sufficiently small `h`:

1. the straight triangles are uniformly shape regular;
2. the curved interface differs from its tangent by `O(K h^2)`;
3. the centered normal segment of length `rho h` on each side remains inside the
   retained triangle for a fixed `rho>0`;
4. the tangential cross-section has length at least `M h`;
5. the normal-coordinate Jacobian has a uniform lower bound, for example `J0=1/2`;
6. at least `c L/h` retained elements cover the arc.

The key perturbation estimate is that the geometric safety margin is `O(h)`, while
curvature moves the interface and straight mesh edges by only `O(Kh^2)`.  Thus a
fixed phase margin survives for all sufficiently small `h`.

### What remains genuinely difficult in 1B

The local lower bound is now routine.  The harder part is the concrete upper recovery:
construct a globally conforming, nonnegative quadratic Bernstein–Bézier field in the
curved strip with `H1` error `O(h^(3/2))`.  A viable route is:

1. use the standard quadratic interpolant away from the strip;
2. express the solution in signed-distance coordinates inside the strip;
3. replace the normal half-quadratic by the explicit positive strip polynomial used in
   1A, with slowly varying amplitude `a(s)`;
4. interpolate the tangential dependence quadratically;
5. use shared Bernstein edge coefficients to preserve conformity;
6. bound tangential and curvature corrections by `O(h^2)` in squared energy, below
   or equal to the leading `O(h^3)` strip contribution after summation.

This route should prove a deterministic theorem for a designed mesh following any
compact regular arc.

---

# Approach 2: generic translations of a periodic triangulation

The strongest clean observation is that transversality to mesh edges is unnecessary.
Instead, retain points of the free boundary that land deep inside triangles.

## 2.1 Eroded triangle cores

Let `Tper` be a periodic shape-regular triangulation of `R^2` with fundamental cell
`Q`.  Choose `r>0` smaller than one quarter of the minimum inradius of the reference
triangles.  For each triangle `T`, define its core

```text
T[-r] = {x in T : dist(x, boundary T) >= r}.
```

Let `G_r` be the union of these cores in one fundamental cell and define

```text
p_r = area(G_r) / area(Q) > 0.
```

Scale by `h` and translate by `tau in Q`.  A point in a scaled core has a Euclidean
ball of radius `r h` contained in its triangle.  Therefore, independently of the
orientation of the free boundary, that triangle contains a centered normal segment
and a tangential segment of fixed length comparable to `h`.  The cut phase is exactly
`1/2` when the fiber is centered at the free-boundary point.

## 2.2 Fubini translation lemma

For a rectifiable free-boundary arc `Gamma0` of length `L`, define

```text
X_h(tau) = H^1({x in Gamma0 : x lies in a translated h-scaled triangle core}).
```

For every fixed `x`, the reduced coordinate `(x/h - tau) mod Q` is uniform as `tau`
ranges uniformly over `Q`.  Hence

```text
E_tau[1_{x is in a core}] = p_r.
```

Fubini gives the exact identity

```text
E_tau[X_h(tau)] = p_r L.
```

Since `0 <= X_h <= L`, the set

```text
A_h = {tau : X_h(tau) >= (p_r/2)L}
```

has normalized measure at least

```text
measure(A_h) >= p_r / (2-p_r).
```

Proof: if `q=measure(A_h)`, then

```text
p_r L <= E[X_h] <= (p_r L/2)(1-q) + L q.
```

Solving yields the stated bound.

Thus for every mesh size `h`, a positive-measure set of translations contains a fixed
positive amount of free boundary in triangle cores.

## 2.3 From good arc length to distinct retained elements

Choose a maximal set of good free-boundary points separated in arclength by `D h`,
where `D` is larger than twice the maximum reference-element diameter.  The balls of
arclength radius `D h` cover the good set, so the number of selected points satisfies

```text
#selected >= X_h(tau)/(2 D h).
```

The selected points lie in distinct or uniformly bounded-overlap triangles.  Shrinking
`r` by a fixed factor, the tubular map

```text
(s,t) -> gamma(s) + t nu(s)
```

on a rectangle of side lengths `c h` and `2 c h` remains inside the triangle around
each selected point.  If the curvature is bounded by `K`, then for `h` small

```text
1/2 <= 1 - t kappa_gamma(s) <= 3/2.
```

Therefore each selected triangle satisfies the certified mapped-prism hypotheses with
uniform constants, and the number of retained elements is at least `N/h`.

## 2.4 Resulting generic-shift theorems

The preceding argument yields several precise statements.

### Per-level existence theorem

For every sufficiently small `h`, there is a positive-measure set of translations for
which the full sharp lower bound holds with constants independent of `h`.

### Deterministically selected translated family

Choose one `tau_h in A_h` at each level.  Then the resulting translated periodic mesh
family satisfies the sharp `h^(3/2)` theorem for every sufficiently small `h`.

### Fixed-shift subsequence theorem

Because every `A_h` has measure bounded below by the same positive number, for any
sequence `h_n -> 0`, the limsup set

```text
limsup_n A_(h_n)
```

has positive measure.  Every shift in this limsup is good for infinitely many levels.
Thus a single fixed translation gives a sharp `h^(3/2)` lower bound along an infinite
subsequence.

### Randomized family

If the translation is sampled independently at each level, the probability of a good
level is uniformly bounded below.  Almost surely there are infinitely many good
levels.  If the implementation resamples until `tau_h in A_h`, the expected number of
samples is uniformly bounded.

## 2.5 What Approach 2 does not automatically give

A single fixed shift need not be good for all sufficiently small `h`.  That stronger
claim requires an arithmetic/equidistribution theorem and can fail for specially
aligned straight interfaces and nested mesh scales.  The robust claims are:

1. good translations exist at every level;
2. they occupy a uniformly positive measure of translation space;
3. one fixed shift is good along an infinite subsequence;
4. independently shifted or resampled meshes provide a practical generic theorem.

---

# Approach 3: arbitrary shape-regular meshes

## 3.1 Universal sharp saturation is false

Use the exact flat solution

```text
u(x,y) = a (y_+)^2.
```

Take a shape-regular triangulation whose skeleton contains the line `y=0`.  On every
triangle below the interface, `u=0`; on every triangle above it, `u=a y^2`.  These are
quadratic polynomials, their traces agree on the interface, and the normal derivative
also vanishes there.  Hence

```text
u belongs to the conforming P2 space.
```

It is obstacle-feasible, so by uniqueness the discrete solution equals the exact
solution.  The finite-element error is zero.  Therefore no theorem of the form

```text
c h^(3/2) <= |u-u_h|_(H1), c>0
```

can hold for all shape-regular meshes.

## 3.2 Near-alignment also destroys a uniform constant

Shift the nearest mesh row so that the free boundary crosses at phase `theta_h`, with
`theta_h -> 0`, while keeping all element aspect ratios uniformly bounded.  The exact
one-dimensional best-error factor is

```text
theta_h^3 (1-theta_h)^3.
```

After summing over `O(1/h)` interface elements in two dimensions, the natural lower
scale becomes

```text
h^(3/2) * theta_h^(3/2).
```

For example, `theta_h=h^beta` produces a scale

```text
h^(3/2 + 3 beta/2),
```

showing that shape regularity alone cannot provide a mesh-independent lower constant.

## 3.3 Correct replacement: a phase-density theorem

For each cut element define a nonnegative quality weight

```text
w_T = J_T M_T a_T^2 theta_T^3 (1-theta_T)^3.
```

The exact local theorem gives

```text
energy_T >= c0 w_T h^(d+2).
```

Hence the global lower bound should depend on the phase-density quantity

```text
D_h = h^(d-1) sum_(T cut) w_T.
```

For quasi-uniform meshes,

```text
|u-v_h|_(H1) >= c h^(3/2) sqrt(D_h).
```

Uniform `h^(3/2)` saturation is recovered exactly when

```text
liminf_(h->0) D_h > 0.
```

Aligned meshes have `D_h=0`.  Uniformly phase-separated meshes have `D_h>=D0>0`.
Generic translations have `D_h>=D0` on the good levels proved in Approach 2.

This phase-density formulation is the appropriate arbitrary-mesh theorem and is a
strict improvement over a false universal statement.

---

# Recommended proof order

1. **Finish 1A:** exact flat obstacle solution, shifted grid, explicit feasible repair,
   exact constants, and a direct invocation of the certified Lean theorem.
2. **Formalize the core-translation lemma from Approach 2:** this is elementary
   measure theory and gives a broad existence/genericity result without difficult
   angle cases.
3. **Prove the phase-weighted cut-patch theorem in Lean:** it captures Approach 3 and
   subsumes both deterministic and generic meshes.
4. **Develop 1B:** curved regular arc and tubular designed mesh.
5. Only after these are complete, investigate stronger fixed-shift equidistribution
   statements.

# Completion estimates

```text
Approach 1A exact flat benchmark:       80-90% human proof; 50-60% Lean instantiation.
Approach 1B curved designed mesh:        60-70% proof architecture; upper recovery remains.
Approach 2 per-level generic shifts:     75-85% proof architecture; measure/packing details remain.
Approach 2 fixed-shift all-level claim:  not established and likely needs extra arithmetic assumptions.
Approach 3 universal arbitrary meshes:   disproved.
Approach 3 phase-density replacement:    75-85% human proof; Lean algebra should be short.
```