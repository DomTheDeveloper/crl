# Global one-dimensional smooth-contact saturation

## Theorem

Fix an integer `p >= 2`. Let `N` be odd, set `h = 2/N`, and let `T_h` be the
uniform partition of `[-1,1]` into `N` intervals. Let `V_h^p` be the continuous
piecewise-polynomial space of degree at most `p` with endpoint values

```text
v(-1) = v(1) = 1.
```

Let `K_h^B` be the subset whose degree-`p` Bernstein coefficients on every
cell lie in `[0,1]`. For

```text
u(x) = x^2,
E_h = inf_{v in K_h^B} ||u-v||_{H^1(-1,1)},
```

define

```text
gamma_p = 1/(4(p-1))  if p is even,
gamma_p = 1/(4p)      if p is odd.
```

Then there are constants `c_p,C_p>0`, independent of `h`, such that

```text
c_p h^2 <= E_h <= C_p h^2.
```

More explicitly, if `Lambda_p` is the operator norm, with respect to the
supremum norm on `P_p([0,1])`, of either central Bernstein coefficient
functional used below, then

```text
(gamma_p/(sqrt(2) Lambda_p)) h^2
    <= E_h
    <= gamma_p sqrt(56/15) h^2.
```

Thus the best approximation order is exactly two for every fixed `p>=2`.

## 1. Cellwise coefficients of `x^2`

On a cell `T=[a,a+h]`, with reference coordinate `x=a+ht`, the exact degree-`p`
Bernstein coefficients of `x^2` are

```text
b_{T,k}
 = a^2 + 2ah k/p + h^2 k(k-1)/(p(p-1)),
0 <= k <= p.
```

Indeed this follows from the exact first and second Bernstein moments.

If `a>=0`, all three terms are nonnegative and the coefficients increase from
`a^2` to `(a+h)^2`. Hence they lie in `[0,1]`. If `a+h<=0`, reflection of the
cell reverses the coefficient vector and gives the same conclusion.

Because `N` is odd, the only cell crossing zero is

```text
T_0=[-h/2,h/2].
```

On this cell,

```text
b_{0,k}=h^2 [k(k-1)/(p(p-1)) - k/p + 1/4].
```

The minimum equals `-gamma_p h^2`. For even `p=2m` it occurs at `k=m`; for odd
`p=2m+1` it occurs at both `k=m,m+1`. Therefore every coefficient of `u` lies
in

```text
[-gamma_p h^2,1].
```

## 2. Global lower bound

Choose one central index attaining the negative coefficient and denote the
corresponding reference coefficient functional by

```text
ell_p : P_p([0,1]) -> R.
```

Let

```text
Lambda_p = sup_{q != 0} |ell_p(q)|/||q||_infinity.
```

This number is finite because `P_p` is finite-dimensional. It is also fully
computable: if `V_p` is the Bernstein collocation matrix at any `p+1`
unisolvent nodes, `Lambda_p` can be bounded by the `l^1` norm of the relevant
row of `V_p^{-1}`.

For any `v_h in K_h^B`, write `e_h=v_h-u`. On the central cell the selected
coefficient satisfies

```text
ell_p(e_h|_{T_0}) >= gamma_p h^2.
```

The pullback to `[0,1]` does not change the supremum norm. Since `e_h(-1)=0`,

```text
||e_h||_{L^infinity(-1,1)}
 <= sqrt(2) ||e_h'||_{L^2(-1,1)}
 <= sqrt(2) ||e_h||_{H^1(-1,1)}.
```

Consequently

```text
gamma_p h^2
 <= Lambda_p ||e_h||_infinity
 <= sqrt(2) Lambda_p ||e_h||_{H^1}.
```

Taking the infimum over `K_h^B` proves the lower estimate.

## 3. Explicit global feasible recovery

Set

```text
d_h = gamma_p h^2,
epsilon_h = d_h/(1+d_h),
v_h = (1-epsilon_h)u + epsilon_h
    = (u+d_h)/(1+d_h).
```

Every coefficient `b` of `u` lies in `[-d_h,1]`, and the corresponding
coefficient of `v_h` is

```text
(b+d_h)/(1+d_h),
```

which lies in `[0,1]`. The endpoint values are preserved because `u(+-1)=1`.
Hence `v_h in K_h^B`.

Moreover,

```text
v_h-u = d_h(1-x^2)/(1+d_h).
```

A direct calculation gives

```text
||1-x^2||_{H^1(-1,1)}^2
 = integral (1-x^2)^2 + integral 4x^2
 = 16/15 + 8/3
 = 56/15.
```

Therefore

```text
E_h <= d_h/(1+d_h) sqrt(56/15)
    <= gamma_p sqrt(56/15) h^2.
```

This completes the global `Theta(h^2)` theorem.

## Consequences

1. For every `p>2`, no mesh-uniform estimate of the form

   ```text
   E_h <= C h^p ||u||_{H^{p+1}}
   ```

   can hold for all smooth bound-touching targets.

2. The seminorm estimate with `|u|_{H^{p+1}}` fails already for `p=2`, since
   that seminorm vanishes for `u=x^2` while `E_h>0`.

3. The obstruction is not caused by regularity or by the unconstrained finite
element space: `u=x^2` belongs exactly to `V_h^p`. It is purely a consequence
of the smaller Bernstein coefficient cone.

4. The theorem is compatible with qualitative Mosco convergence. The error
still tends to zero, but it saturates at second order.
