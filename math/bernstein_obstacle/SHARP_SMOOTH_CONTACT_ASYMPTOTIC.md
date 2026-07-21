# Sharp asymptotic constant for smooth quadratic contact

## Status

This note records a stronger theorem target suggested by the exact coefficient
obstruction and confirmed numerically.  The two-sided `Theta(h^2)` result is
already proved at the human-mathematics level.  The limit theorem below still
requires a complete compactness and recovery proof, followed by Lean
formalization.

## Setting

Let `p >= 2` be fixed.  On `Omega=(-1,1)`, let

```text
u(x)=x^2.
```

Use uniform meshes with an odd number of cells and mesh width `h`, so the contact
point `x=0` remains at the midpoint of the central cell.  Let `K_h^B` be the
continuous degree-`p` finite-element functions with nonnegative local Bernstein
coefficients and exact endpoint values `v_h(-1)=v_h(1)=1`.  Write

```text
E_h = inf_{v_h in K_h^B} ||v_h-u||_{H1(-1,1)}.
```

Define

```text
gamma_p = 1/[4(p-1)]  if p is even,
gamma_p = 1/(4p)      if p is odd.
```

The central Bernstein coefficient of `u` is exactly `-gamma_p h^2`.

## Sharp-limit conjecture

The predicted exact asymptotic constant is

```text
lim_{h -> 0} E_h/h^2
  = gamma_p sqrt(2/tanh(1)).                         (1)
```

The same limit should hold for bilateral coefficient bounds `[0,1]`, because the
upper constraint is asymptotically inactive for the recovery sequence described
below.

## 1. Limiting variational problem

Set

```text
w_h = (v_h-u)/h^2.
```

Central coefficient feasibility gives

```text
L_h(w_h) >= gamma_p,                                 (2)
```

where `L_h` extracts the relevant central Bernstein coefficient.  On the central
cell, fixed-degree norm equivalence and scaling imply

```text
|L_h(w_h)-w_h(0)|
  <= C_p h^(1/2) ||w_h'||_{L2(-h/2,h/2)}.            (3)
```

Hence every bounded `H1` sequence satisfying (2) has a weak limit `w in H_0^1`
with

```text
w(0) >= gamma_p.                                    (4)
```

The limiting lower-bound problem is therefore

```text
minimize ||w||_{H1(-1,1)}
subject to w in H_0^1(-1,1), w(0) >= gamma_p.        (5)
```

## 2. Exact Green-profile minimizer

Let `G` be the Riesz representer of point evaluation at zero for the full `H1`
inner product

```text
<a,b> = integral (a b + a' b').
```

Then `G` solves

```text
-G''+G = delta_0,
G(-1)=G(1)=0,
```

and is explicitly

```text
G(x) = sinh(1-|x|)/(2 cosh(1)).
```

Therefore

```text
G(0) = tanh(1)/2,
||evaluation at 0||^2 = tanh(1)/2.
```

The normalized minimizer of (5) is

```text
phi(x) = sinh(1-|x|)/sinh(1),
```

with

```text
phi(0)=1,
||phi||_{H1}^2 = 2/tanh(1).
```

Thus the lower bound predicted by (5) is exactly

```text
gamma_p sqrt(2/tanh(1)).                             (6)
```

## 3. Recovery sequence

Let `P_h^1 phi` be the continuous piecewise-linear interpolant of `phi` on the
same symmetric mesh.  Its nodal values are nonnegative, hence every degree-`p`
Bernstein coefficient of the degree-elevated function is nonnegative.

On the central cell the interpolant is constant, because the endpoint values are
equal by symmetry.  Put

```text
s_h = phi(h/2),
alpha_h = gamma_p/s_h,
v_h = u + alpha_h h^2 P_h^1 phi.                     (7)
```

The bad central coefficient becomes exactly zero.  Every other lower-bound
coefficient remains nonnegative.  The endpoint data remain exact because
`phi(+-1)=0`.  Moreover

```text
s_h -> 1,
P_h^1 phi -> phi strongly in H1.
```

Consequently

```text
||v_h-u||_{H1}/h^2
  -> gamma_p ||phi||_{H1}
   = gamma_p sqrt(2/tanh(1)).                        (8)
```

For the bilateral cone `[0,1]`, one must additionally show that the positive
correction in (7) remains below the coefficientwise upper slack near the domain
boundary.  Since `1-x^2` vanishes linearly while the correction is `O(h^2)` times
a linearly vanishing function, this holds for sufficiently small `h`.

## 4. Numerical confirmation

Global continuous Bernstein-coefficient quadratic programs were solved with the
exact assembled `H1` Gram matrix and coefficient box constraints.  The values of
`E_h/h^2` converge toward (1).

Representative data:

```text
p   predicted constant   N=17       N=33       N=65
2   0.405129             0.377612   0.390077   0.397230
3   0.135043             0.133410   0.134176   0.134596
4   0.135043             0.107943   0.118831   0.126036
5   0.081026             0.077538   0.079165   0.080067
6   0.081026             0.050876   0.053908   0.059171
```

Even degrees above two converge more slowly because several near-central
coefficient constraints remain relevant at finite `h`, but the trend is
consistent with the same point-evaluation limit.

## 5. Proof obligations

A complete theorem needs:

1. uniform local coefficient-functional estimate (3);
2. equicoercivity of scaled near-minimizers;
3. weak lower semicontinuity and passage from `L_h` to point evaluation;
4. coefficientwise feasibility of the recovery sequence (7) on every cell;
5. eventual upper-bound feasibility for the bilateral cone;
6. convergence of the piecewise-linear Green-profile interpolant in `H1`;
7. Lean formalization of the Green function and the liminf/limsup argument.

This limit theorem would sharpen the second-order saturation result from an order
classification to an exact asymptotic law.
