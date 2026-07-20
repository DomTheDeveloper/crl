# Venue manuscript update V4

The venue-ready manuscript has been rebuilt after the adversarial proof audit and the mechanics-validation campaign.

## Analytical corrections now incorporated

1. The positive Bernstein sampling estimate is stated in the dimension-safe form
   \[
   \|w-\mathcal B_T^r w\|_{L^2(T)}
   \le C h_T^2 |T|^{1/2}\|D^2w\|_{L^\infty(T)},
   \]
   \[
   \|\nabla(w-\mathcal B_T^r w)\|_{L^2(T)}
   \le C h_T |T|^{1/2}\|D^2w\|_{L^\infty(T)}.
   \]
2. General barycentric-lattice unisolvence is proved by an explicit cardinal basis
   \[
   L_\alpha(\lambda)=
   \prod_i \frac1{\alpha_i!}
   \prod_{m=0}^{\alpha_i-1}(r\lambda_i-m).
   \]
3. The sharp theorem requires a mesh-independent one-sided `H^{r+1}` extension near the regular free boundary.
4. The risky-element coefficient estimate is two-sided:
   \[
   |b_{T,\alpha}(I_h^r u)|\le C h_\Gamma^2.
   \]

## Mechanics validation added

### Three-dimensional spherical-contact test

- tensor-product degrees 1--3;
- nonnegative control coefficients in every run;
- sampled minimum nonnegative to roundoff;
- KKT residual below `9e-17`;
- independent bound-constrained optimizer cross-check.

### Plane-strain Hertz--Signorini contact

At nearly the same algebraic size:

| Method | Unknowns | Hertz half-width error | Pressure L2 error | Minimum gap |
|---|---:|---:|---:|---:|
| Linear triangles | 20,513 | `4.997e-3` | `3.230e-1` | 0 |
| Quadratic Bernstein--Bézier | 20,193 | `1.022e-4` | `2.049e-1` | 0 |

The quadratic edge-gap coefficients certify nonpenetration over each complete contact edge. The half-width error is approximately 48.9 times smaller than the linear result at comparable size.

## Lean scope stated in the paper

The manuscript reports the verified finite certificate, clipping, coefficient range, interval/cube no-penetration, and simplicial certificate layer. It explicitly does not claim that the Mosco or free-boundary theorem has been fully formalized.

## Build/preflight

- 18 pages;
- 216-word abstract;
- six keywords;
- two clean `pdflatex` passes;
- no undefined citations or references;
- no overfull boxes;
- all rendered pages visually inspected;
- PDF openable, text-based, unencrypted.

The analytical theorem remains awaiting independent expert endorsement through issues #98--#101.