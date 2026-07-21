# Corrected Bernstein-coefficient recovery theorem

## 1. Setting

Let `V_h^p` be a conforming degree-`p` finite-element space with globally shared
Bernstein degrees of freedom.  Split the global coefficients into fixed trace
coefficients and free coefficients.  Let

```text
K_h^B = {v_h in V_h^p : m <= b_a(v_h) <= M for every free coefficient a,
                         and v_h has the prescribed discrete trace}.
```

Let `I_h u` be any conforming unconstrained recovery with the correct trace.
Define its free-coefficient violation

```text
delta_h(u) = max_a max((m - b_a(I_h u))_+, (b_a(I_h u) - M)_+).
```

Assume there is a same-trace feasible anchor `z_h in K_h^B` with free-coefficient
margin `rho_h > 0`:

```text
m + rho_h <= b_a(z_h) <= M - rho_h
```

for every free coefficient.

## 2. Explicit inward repair

Set

```text
epsilon_h = delta_h / (rho_h + delta_h),
R_h u      = (1 - epsilon_h) I_h u + epsilon_h z_h.
```

Every fixed trace coefficient is preserved because `I_h u` and `z_h` have the
same trace.  For a free lower-bound coefficient,

```text
b_a(R_h u)
  >= (1-epsilon_h)(m-delta_h) + epsilon_h(m+rho_h)
   = m.
```

The upper bound is identical.  Hence `R_h u in K_h^B`.

## 3. Corrected error estimate

The exact identity

```text
R_h u = I_h u + epsilon_h (z_h - I_h u)
```

gives

```text
||u - R_h u||_{H1}
  <= ||u - I_h u||_{H1}
     + epsilon_h ||z_h - I_h u||_{H1}.
```

Since

```text
epsilon_h <= delta_h / rho_h,
```

we obtain

```text
||u - R_h u||_{H1}
  <= ||u - I_h u||_{H1}
     + (delta_h/rho_h) ||z_h - I_h u||_{H1}.        (1)
```

This is the correct replacement for an unconditional pure `O(h^p)` theorem.

## 4. Rate consequence

Suppose uniformly in `h` that

```text
||u-I_h u||_{H1} <= C_I h^p,
rho_h >= rho_0 > 0,
||z_h-I_h u||_{H1} <= C_z,
delta_h(u) <= C_delta h^q.
```

Then

```text
inf_{v_h in K_h^B} ||u-v_h||_{H1}
  <= C_I h^p + (C_delta C_z/rho_0) h^q
  <= C h^{min(p,q)}.                                (2)
```

The smooth quadratic-contact theorem proves that `q=2` is sharp on a persistent
phase-misaligned family.  Therefore no theorem can replace `min(p,q)` by `p`
without an assumption forcing `q >= p` or eliminating the bad phase geometrically.

## 5. How to estimate `delta_h`

For a fixed-degree affine-reproducing local recovery, coefficient extraction is a
bounded functional on the reference polynomial space.  Taylor expansion about the
associated barycentric lattice point gives

```text
|b_{T,alpha}(I_h u) - u(x_{T,alpha})|
  <= C_p sum_{j=2}^{p+1} h_T^j |u|_{W^{j,infinity}(omega_T)}.   (3)
```

Near a contact set where

```text
u-m = O(dist(.,Gamma)^q)
```

and the corresponding derivatives satisfy

```text
|D^j(u-m)| <= C dist(.,Gamma)^{q-j},  0 <= j <= q,
```

formula (3) gives

```text
delta_T(u) <= C h_T^q.                              (4)
```

Combining (2) and (4) gives the contact-order law

```text
best H1 rate <= C h^{min(p,q)}.
```

For `q=2`, the explicit `u=x^2` family proves matching second-order saturation.
For `q>=p`, the repair no longer lowers the standard degree-`p` rate.

## 6. Boundary conditions

A constant interior anchor is not sufficient in general because it can destroy
Dirichlet data.  The theorem requires a **same-trace discrete Slater anchor**:

```text
z_h|_{partial Omega} = g_h,
```

with strict margin only on free coefficients.  Fixed boundary coefficients may lie
exactly at `m` or `M`; they are unchanged by the blend.

## 7. Bilateral bounds

For both lower and upper bounds use the same `delta_h`, defined as the maximum of
both violations.  The single blend toward a bilateral interior anchor repairs both
sides simultaneously.

## 8. Mosco and variational inequalities

The recovery theorem supplies the strong-limsup half of Mosco convergence whenever
`delta_h -> 0`, even if its rate is only `h^2`.  The weak-liminf half follows from

```text
K_h^B subset K
```

and weak closedness of the continuous convex admissible set.  Therefore qualitative
VI convergence can hold despite second-order saturation of the high-order cone.

A quantitative Falk/Cea estimate transfers (1) to the discrete PDE solution:

```text
||u-u_h^B||_V
  <= C [best approximation in K_h^B + consistency terms].
```

The solution rate is consequently limited by `h^{min(p,q)}` unless alignment,
clearance, or higher-order flatness removes the coefficient defect.

## 9. Sharpness and interpretation

The result separates three issues that were previously conflated:

1. ordinary polynomial approximation;
2. pointwise bound preservation;
3. coefficient-cone feasibility.

For `u=x^2`, issue 1 has zero error and issue 2 is exact, while issue 3 alone creates
the `Theta(h^2)` barrier.  Thus the added term in (1) is not a proof artifact; it is
the sharp price of the computationally convenient coefficient cone.
