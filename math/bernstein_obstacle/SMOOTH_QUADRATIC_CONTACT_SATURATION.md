# Smooth quadratic-contact saturation of fixed-degree Bernstein coefficient cones

## Purpose

This note addresses the precise approximation gap left open by Kirby--Shapero:
for a continuous degree-`p` finite-element space, how much approximation power is
lost when one requires every local degree-`p` Bernstein coefficient to satisfy the
pointwise bounds?

The answer is negative in full generality.  Even an analytic quadratic function,
represented exactly by the unconstrained finite-element space, can have a negative
local degree-`p` Bernstein coefficient on every mesh in a shape-regular phase-locked
family.  The best coefficient-feasible approximation then has sharp `H^1` order
`h^2`, independently of `p`.

This is a coefficient-cone obstruction.  It is distinct from the previously
formalized `h^(3/2)` half-quadratic hinge obstruction, which comes from the limited
Sobolev regularity of a function such as `(x_+)^2` across an active/free boundary.

---

## Setting

Fix an integer `p >= 2`.  Let

```text
Omega = [-1,1],

u(x) = x^2,

m = 0,
M = 1.
```

For every odd integer `N`, let `T_h` be the uniform partition of `[-1,1]` into
`N` intervals of length

```text
h = 2/N.
```

Because `N` is odd, the origin lies at phase `1/2` in the unique central element

```text
T_0 = [-h/2,h/2].
```

Let `V_h^p` be the continuous piecewise-polynomial space of degree at most `p`,
with the exact Dirichlet data

```text
v_h(-1) = v_h(1) = 1.
```

Let `K_h^B` consist of the functions in `V_h^p` whose degree-`p` Bernstein
coefficients on every element lie in `[0,1]`.

The exact function `u` belongs to `V_h^p` and satisfies the exact boundary data,
but need not belong to `K_h^B`.

---

## Exact central-element coefficient formula

Use the central-element coordinate

```text
x = h (t - 1/2),    0 <= t <= 1.
```

Then

```text
u(x) = h^2 (t - 1/2)^2.
```

The standard degree-`p` Bernstein identities are

```text
t   = sum_{k=0}^p (k/p) B_k^p(t),

t^2 = sum_{k=0}^p (k(k-1)/(p(p-1))) B_k^p(t).
```

Therefore the coefficient at index `k` is

```text
beta_{p,k}(h)
  = h^2 [ k(k-1)/(p(p-1)) - k/p + 1/4 ].
```

Writing

```text
k = p/2 + r
```

(with integral `r` for even `p` and half-integral `r` for odd `p`) gives

```text
beta_{p,k}(h)
  = - h^2 (p - 4 r^2) / [4 p (p-1)].
```

Choose an index nearest to `p/2`.  Define

```text
gamma_p = 1/[4(p-1)]   when p is even,

gamma_p = 1/(4p)       when p is odd.
```

Then one central coefficient is exactly

```text
-gamma_p h^2 < 0.
```

Thus `u` is an analytic, pointwise nonnegative function lying in the unconstrained
finite-element space, but `u` is excluded from the computational Bernstein cone on
every mesh in the family.

For `p = 3`, the identity is especially transparent:

```text
(t - 1/2)^2
  = (1/4) B_0^3(t)
    - (1/12) B_1^3(t)
    - (1/12) B_2^3(t)
    + (1/4) B_3^3(t).
```

---

## Theorem: sharp second-order saturation

There exist constants `0 < c_p <= C_p`, depending on `p` but not on `h`, such
that for every odd `N` sufficiently large,

```text
c_p h^2
  <= inf_{v_h in K_h^B} ||u-v_h||_{H^1(-1,1)}
  <= C_p h^2.
```

### Lower bound

Let `j_p` be a nearest integer to `p/2`, and let `b_{j_p}` denote coefficient
extraction in the degree-`p` Bernstein basis on the reference interval.

For every `v_h in K_h^B`, on the central element,

```text
b_{j_p}(v_h-u)
  >= gamma_p h^2.
```

Since coefficient extraction is a continuous linear functional on the fixed
finite-dimensional space `P_p`, there is a constant `A_p` such that

```text
|b_{j_p}(q)| <= A_p ||q||_{L-infinity(0,1)}
```

for every `q in P_p`.  Pullback preserves the supremum norm.  The one-dimensional
Sobolev embedding has a mesh-independent constant `C_emb`:

```text
||w||_{L-infinity(-1,1)} <= C_emb ||w||_{H^1(-1,1)}.
```

Consequently

```text
gamma_p h^2
  <= A_p C_emb ||v_h-u||_{H^1(-1,1)}.
```

This proves the lower bound with

```text
c_p = gamma_p/(A_p C_emb).
```

### Upper bound preserving both bounds and the exact boundary data

Put

```text
d_h       = gamma_p h^2,

epsilon_h = d_h/(1+d_h),

v_h(x)    = (1-epsilon_h) x^2 + epsilon_h.
```

The function `v_h` is a global quadratic, hence belongs to every `V_h^p`.
Moreover,

```text
v_h(-1) = v_h(1) = 1,
```

so the exact Dirichlet data are preserved.

On every element not crossing the origin, the degree-2 Bernstein coefficients of
`x^2` are

```text
a^2, a(a+h), (a+h)^2,
```

which are nonnegative.  Degree elevation preserves coefficient nonnegativity.  On
the central element, the minimum degree-`p` coefficient is `-d_h`.  Every local
coefficient of `x^2` is at most `1`.  Since the constant polynomial `1` has every
Bernstein coefficient equal to `1`, every coefficient of `v_h` lies in `[0,1]`:

```text
(1-epsilon_h)(-d_h) + epsilon_h = 0,

(1-epsilon_h)(1) + epsilon_h = 1.
```

Therefore `v_h in K_h^B`.

Finally,

```text
v_h-u = epsilon_h (1-x^2),
```

and

```text
||1-x^2||_{H^1(-1,1)}^2 = 56/15.
```

Hence

```text
||v_h-u||_{H^1(-1,1)}
  = epsilon_h sqrt(56/15)
  <= gamma_p sqrt(56/15) h^2.
```

This proves the upper bound.

---

## Immediate consequences

### 1. The universal optimal `O(h^p)` theorem is false for every `p >= 3`

The function `u(x)=x^2` has a fixed finite `H^{p+1}` norm.  The sharp lower bound
is `c_p h^2`, which cannot be bounded by `C h^p` with a mesh-independent constant
when `p > 2`.

Therefore no theorem of the form

```text
inf_{v_h in K_h^B} ||u-v_h||_{H^1}
  <= C h^p ||u||_{H^{p+1}}
```

can hold for all smooth bounded functions touching a bound and all shape-regular
mesh families.

### 2. A seminorm-only estimate fails already for `p = 2`

For every `p >= 2`,

```text
|u|_{H^{p+1}} = 0.
```

But `u` is not in `K_h^B`, and the best constrained error is positive.  Thus an
estimate with only `|u|_{H^{p+1}}` on the right cannot be true even for quadratic
elements.

### 3. Polynomial reproduction is lost at active contact

The unconstrained finite-element space reproduces `u` exactly.  The
coefficient-constrained cone does not.  The loss is not caused by interpolation,
mesh distortion, nonconformity, boundary approximation, or PDE consistency.  It is
caused solely by the strict inclusion

```text
{coefficient-bounded polynomials}
  subsetneq
{pointwise-bounded polynomials}.
```

### 4. Degree elevation and mesh refinement are different mechanisms

Bernstein positivity says that a strictly positive polynomial eventually has
nonnegative coefficients after enough degree elevation.  Here the polynomial has an
interior zero.  At fixed finite element degree `p`, refining a phase-misaligned mesh
scales the negative coefficient by `h^2` but does not change its sign.

---

## Correct replacement for the false theorem

The natural fixed-degree estimate is a saturation estimate

```text
inf_{v_h in K_h^B} ||u-v_h||_{H^1}
  <= C [ h^p |u|_{H^{p+1}} + repair_h(u) ],
```

where `repair_h(u)` measures the distance of the unconstrained coefficient vector to
the coefficient box.

For a conforming interpolant `I_h u`, define

```text
eta_h(u)
  = max over free Bernstein degrees of freedom of
      (m-b_a(I_hu))_+ and (b_a(I_hu)-M)_+.
```

Affine reproduction and fixed-degree Bramble--Hilbert estimates give, for
`u in W^{2,infinity}`,

```text
eta_h(u) <= C h^2 |u|_{W^{2,infinity}}.
```

If there exists a same-trace feasible anchor `z_h` with

```text
m+delta <= b_a(z_h) <= M-delta
```

on all free coefficients, with `delta > 0` and uniformly bounded `H^1` norm, set

```text
lambda_h = eta_h/(delta+eta_h),

R_hu = (1-lambda_h) I_hu + lambda_h z_h.
```

Coefficient convexity gives `R_hu in K_h^B`, conformity and boundary data are
preserved, and

```text
||u-R_hu||_{H^1}
  <= C [h^p |u|_{H^{p+1}} + eta_h(u)]
  <= C [h^p |u|_{H^{p+1}} + h^2 |u|_{W^{2,infinity}}].
```

The quadratic example proves that the `h^2` term is sharp in general.

Under higher-order contact flatness, `eta_h(u)` can be smaller.  If the first
nonzero contact term has order `q` and the corresponding phase polynomial has a
negative degree-`p` Bernstein coefficient, the expected sharp fixed-degree rate is

```text
h^{min(p,q)}
```

under a bounded same-trace repair anchor.  Thus `O(h^p)` requires contact order at
least `p`, or a fitted/aligned mesh that removes the offending phase.

---

## Relation to the half-quadratic `h^(3/2)` theorem

The profile

```text
u(x) = (x_+)^2
```

has a jump in its second derivative.  Its best piecewise-polynomial `H^1`
approximation on an unfitted element already has an `h^(3/2)` obstruction, even
without coefficient constraints.  That theorem describes free-boundary regularity
and phase geometry.

The present theorem uses

```text
u(x) = x^2,
```

which is analytic and belongs exactly to the unconstrained finite-element space.
Its `h^2` error is therefore a pure Bernstein coefficient-cone saturation effect.
The two results are complementary and must not be conflated.

---

## Mosco and variational-inequality consequences

The negative rate theorem does not preclude qualitative convergence.  The degree-1
bounded finite-element cone embeds in the degree-`p` Bernstein cone by degree
elevation:

```text
K_h^{P1} subset K_h^B subset K.
```

Subject to the standard bounded-density and trace-compatibility hypotheses, this
provides the strong recovery half of Mosco convergence, while convex weak closure of
`K` gives the liminf half.  Hence the discrete variational inequalities can converge
without retaining the formal order `p`.

For coercive problems, the Cea/Falk estimate then transfers the corrected
approximation rate, not the false universal `h^p` rate:

```text
||u-u_h^B||_{H^1}
  <= C inf_{v_h in K_h^B} ||u-v_h||_{H^1}.
```

For smooth quadratic contact and `p>2`, the coefficient cone can therefore force a
second-order saturation of the discrete solution even though the unconstrained
Galerkin method reproduces the solution exactly.

---

## Formalization targets

1. Prove the cubic identity

```text
(t-1/2)^2
  = 1/4 B_0^3 - 1/12 B_1^3 - 1/12 B_2^3 + 1/4 B_3^3.
```

2. Prove the general degree-`p` coefficient formula and parity-specialized
   negativity constant `gamma_p`.
3. Define the odd uniform mesh and central-element pullback.
4. Prove the explicit feasible repair

```text
v_h = (1-epsilon_h)x^2 + epsilon_h.
```

5. Connect coefficient extraction to the one-dimensional Sobolev embedding for the
   lower bound.
6. State the terminal sharp `Theta(h^2)` best-approximation theorem.
7. Add a separate theorem making explicit that the existing half-quadratic
   `h^(3/2)` result is a regularity obstruction, not the smooth coefficient-cone
   saturation theorem proved here.
