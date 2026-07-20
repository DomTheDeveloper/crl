# General barycentric-lattice unisolvence

The coefficient-to-grid-value argument uses the inverse of the Bernstein
collocation matrix at the degree-`r` simplex lattice. The following direct
argument closes the general-degree unisolvence dependency.

Let

```text
A_r = {alpha in N_0^(d+1) : |alpha| = r}.
```

On the reference simplex, with barycentric coordinates
`lambda_0, ..., lambda_d`, define for each `alpha in A_r`

```text
L_alpha(lambda)
  = product_{i=0}^d [ 1 / alpha_i! *
      product_{m=0}^{alpha_i-1} (r lambda_i - m) ].
```

The total degree is `sum_i alpha_i = r`, so `L_alpha` belongs to `P_r`.
At the lattice point `lambda = beta/r`:

- when `beta = alpha`, the `i`th inner product equals `alpha_i!`, hence
  `L_alpha(alpha/r) = 1`;
- when `beta != alpha` but `|beta| = |alpha| = r`, there is an index `i`
  with `beta_i < alpha_i`. The inner product then contains the factor with
  `m = beta_i`, which is zero. Hence `L_alpha(beta/r) = 0`.

Therefore

```text
L_alpha(beta/r) = delta_{alpha,beta}.
```

The cardinal family has exactly `binomial(r+d,d) = dim P_r` members. Thus the
evaluation map from `P_r` to values on the degree-`r` barycentric lattice is
bijective, and the lattice is unisolvent in every degree and dimension.
Because the degree-`r` Bernstein polynomials also form a basis of `P_r`, their
collocation matrix at these nodes is invertible.

This is consistent with the explicit cardinal formulas in:

G. Jaklic, J. Kozak, M. Krajnc, V. Vitrih, and E. Zagar,
“Barycentric coordinates for Lagrange interpolation over lattices on a
simplex,” Numerical Algorithms 48 (2008), 93–104,
DOI 10.1007/s11075-008-9178-7.
