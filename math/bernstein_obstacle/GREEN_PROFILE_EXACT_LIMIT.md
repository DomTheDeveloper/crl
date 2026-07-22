# Exact Green-profile asymptotic for smooth quadratic contact

## Statement

Fix `p>=2`. For the odd uniform meshes and coefficient cone in
`GLOBAL_ONE_DIMENSIONAL_SATURATION.md`, let

```text
E_h = inf_{v_h in K_h^B} ||x^2-v_h||_{H^1(-1,1)}.
```

Then

```text
lim_{h -> 0, N=2/h odd} E_h/h^2
  = gamma_p sqrt(2/tanh(1)).
```

Here

```text
gamma_p = 1/(4(p-1))  for even p,
gamma_p = 1/(4p)      for odd p.
```

The normalized Green profile is

```text
phi(x) = sinh(1-|x|)/sinh(1).
```

It belongs to `H_0^1(-1,1)`, satisfies `phi(0)=1`, and

```text
||phi||_{H^1(-1,1)}^2 = 2/tanh(1).
```

## 1. The limiting variational problem

Equip `H_0^1(-1,1)` with

```text
<w,z> = integral_{-1}^1 (wz+w'z').
```

Let

```text
G(x) = (tanh(1)/2) phi(x).
```

On each side of zero, `-G''+G=0`, and the derivative jump at zero is `-1`.
Integration by parts therefore gives

```text
<G,w> = w(0)
```

for every `w in H_0^1(-1,1)`. Thus `G` is the Riesz representer of point
evaluation. Since `G(0)=tanh(1)/2`,

```text
||G||^2 = tanh(1)/2,
||evaluation at 0|| = sqrt(tanh(1)/2).
```

Consequently

```text
min {||w||_{H^1} : w(0)>=gamma_p}
 = gamma_p/||evaluation||
 = gamma_p sqrt(2/tanh(1)),
```

and the unique minimum-norm element is `gamma_p phi`.

## 2. Liminf inequality

Choose a sequence of feasible near-minimizers `v_h` such that

```text
||v_h-u|| <= E_h+o(h^2),
u(x)=x^2.
```

The global upper bound gives `E_h=O(h^2)`. Set

```text
e_h=v_h-u,
w_h=e_h/h^2.
```

Then `w_h` is bounded in `H_0^1(-1,1)`. After passing to a subsequence,

```text
w_h weakly -> w in H_0^1,
w_h -> w uniformly on [-1,1].
```

The uniform convergence follows from the one-dimensional compact embedding:
bounded `H^1` sets are uniformly bounded and uniformly `1/2`-Holder.

Let `ell_{p,j}` be a central Bernstein coefficient functional on the reference
cell, and let

```text
q_h(t)=e_h(h(t-1/2)),  0<=t<=1.
```

The functional

```text
q -> ell_{p,j}(q)-q(1/2)
```

vanishes on constants. Since `P_p([0,1])` is finite-dimensional, there is a
constant `C_p` such that

```text
|ell_{p,j}(q)-q(1/2)| <= C_p ||q'||_{L^2(0,1)}.
```

Under the cell pullback,

```text
||q_h'||_{L^2(0,1)}
 = sqrt(h) ||e_h'||_{L^2(-h/2,h/2)}.
```

Because `||e_h||_{H^1}=O(h^2)`,

```text
|ell_{p,j}(e_h)-e_h(0)|/h^2 = O(sqrt(h)) -> 0.
```

Feasibility gives

```text
ell_{p,j}(e_h) >= gamma_p h^2.
```

Therefore `w(0)>=gamma_p`. Weak lower semicontinuity and the limiting
variational problem yield

```text
liminf E_h/h^2
 >= ||w||_{H^1}
 >= gamma_p sqrt(2/tanh(1)).
```

## 3. Green-profile recovery sequence

Let `I_h^1 phi` be the continuous piecewise-linear nodal interpolant of `phi`
on the odd uniform mesh. The two endpoints of the central cell are `+-h/2`,
and `phi` is even, so `I_h^1 phi` is constant on that cell, equal to

```text
c_h=phi(h/2).
```

Define

```text
r_h = (gamma_p h^2/c_h) I_h^1 phi,
v_h = u+r_h.
```

### Lower coefficient bound

The degree-`p` Bernstein coefficients of a piecewise-affine nonnegative
function are its values at the degree-`p` barycentric lattice points, so all
coefficients of `r_h` are nonnegative. On the central cell they are all exactly
`gamma_p h^2`. Thus they cancel the worst coefficient `-gamma_p h^2` of `u`.
All noncentral coefficients of `u` are already nonnegative. Hence every lower
coefficient bound is satisfied.

### Upper coefficient bound

On any cell `T=[a,a+h]`, the degree-`p` coefficient of `u=x^2` at index `k`
is no greater than its value at the corresponding lattice point:

```text
u(a+hk/p)-b_{T,k}(u)
 = h^2 k(p-k)/(p^2(p-1)) >= 0.
```

The coefficient of the affine function `r_h` is exactly its value at that
lattice point. It therefore suffices to prove `u+r_h<=1` pointwise.

At every mesh node,

```text
phi(x) <= coth(1)(1-x^2).
```

Indeed, with `s=1-|x|`,

```text
sinh(s) <= s cosh(1),
1-x^2=s(2-s)>=s.
```

Linear interpolation preserves the nodal inequality, and the concavity of
`1-x^2` gives

```text
I_h^1 phi <= coth(1) I_h^1(1-x^2)
           <= coth(1)(1-x^2).
```

Since `c_h->1`, for all sufficiently small `h`,

```text
(gamma_p h^2/c_h)coth(1) <= 1.
```

Thus `r_h<=1-u`, so all upper Bernstein coefficient bounds hold. The endpoint
values are unchanged because `I_h^1 phi(+-1)=0`.

### Norm limit

The profile is smooth on each open half interval and has only a derivative
jump at zero. Standard interpolation estimates away from the central cell,
together with a direct estimate on the central cell, give

```text
I_h^1 phi -> phi strongly in H^1(-1,1).
```

Also `c_h=phi(h/2)->1`. Therefore

```text
||v_h-u||/h^2
 = (gamma_p/c_h)||I_h^1 phi||_{H^1}
 -> gamma_p ||phi||_{H^1}
 = gamma_p sqrt(2/tanh(1)).
```

Hence

```text
limsup E_h/h^2
 <= gamma_p sqrt(2/tanh(1)).
```

Combining liminf and limsup proves the exact limit.

## Significance

The exact constant identifies the coefficient cone's asymptotic penalty as a
trace-capacity problem. The local negative coefficient supplies the limiting
constraint `w(0)>=gamma_p`; the ambient Sobolev norm spreads the cheapest
repair globally according to the Green function of `-d^2/dx^2+1` with zero
boundary data.
