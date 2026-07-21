# Contact-aware mesh fitting and adaptive restoration of high order

## 1. Exact aligned-contact theorem in one dimension

Let `p >= 2`, `a >= 0`, and consider the element adjacent to a contact point,
parameterized outward from contact by

```text
x = h t,  0 <= t <= 1.
```

For the pure quadratic profile

```text
u(x)-m = a x^2 = a h^2 t^2,
```

the degree-`p` Bernstein coefficients are

```text
b_k = a h^2 k(k-1)/(p(p-1)),  0 <= k <= p.
```

Every coefficient is nonnegative.  Therefore the exact polynomial belongs to the
coefficient cone on the aligned element.  The same statement holds on the other
side after orienting the local coordinate away from the contact point.

Consequently, if the contact point is inserted as a mesh vertex, the smooth
quadratic target `u=x^2` is represented exactly and the phase-misaligned `h^2`
obstruction disappears completely.

## 2. Simplicial codimension-one version

Let a fitted simplex have a contact face `lambda_0=0`, where `lambda_0` is the
barycentric coordinate normal to that face.  For

```text
u-m = a lambda_0^2,  a >= 0,
```

the degree-`p` simplicial Bernstein coefficient indexed by
`alpha=(alpha_0,...,alpha_d)`, `|alpha|=p`, is

```text
b_alpha = a alpha_0(alpha_0-1)/(p(p-1)) >= 0.
```

Thus a pure normal quadratic contact profile is exactly coefficient-feasible on a
mesh fitted to the contact interface.

More generally, a monomial `a lambda_0^q` with `q <= p` has coefficient

```text
b_alpha
 = a (alpha_0)_q/(p)_q,
```

where `(r)_q=r(r-1)...(r-q+1)`.  These coefficients are nonnegative.  Therefore
contact-order monomials are naturally compatible with face-fitted Bernstein
meshes.

## 3. Curved interfaces

Let `Gamma` be `C^{p+1}` and let a fitted or isoparametric element use a normal
coordinate `s` satisfying

```text
u-m = a(y) s^q + R(y,s),
|D^j R| <= C |s|^{q+1-j}.
```

The leading term has nonnegative Bernstein coefficients on an interface-fitted
reference element.  The remainder contributes a coefficient defect of order
`h^{q+1}`.  Hence the inward repair term is one order smaller than the leading
contact scale.

For `q >= p`, this restores the standard `H1` rate `O(h^p)`.  For analytic data
and geometrically accurate hp meshes, it opens the route to exponential
convergence; p-enrichment alone on a persistently misaligned element does not.

## 4. Why ordinary refinement is not enough

The obstruction depends on the phase

```text
theta_T = position of the contact point inside T.
```

If a refinement rule reproduces a phase bounded away from the endpoints, the
negative coefficient remains `-c(theta,p) h_T^2`.  The cell becomes smaller but the
formal order remains two.

For the midpoint example, bisection at the midpoint inserts the contact point and
eliminates the defect immediately.  A generic blind refinement rule need not do so.
The adaptive operation must resolve **contact geometry**, not merely decrease the
cell diameter.

## 5. Proposed estimator

For an unconstrained high-order recovery `I_h u`, define the local coefficient
violation

```text
delta_T = max_alpha max((m-b_{T,alpha}(I_hu))_+,
                        (b_{T,alpha}(I_hu)-M)_+).
```

Combine it with the ordinary residual estimator:

```text
eta_T^2 = eta_res,T^2
        + C_coeff delta_T^2 h_T^{d-2}
        + C_geom eta_Gamma,T^2.
```

Here `eta_Gamma,T` measures uncertainty in the reconstructed contact location or
normal direction.

The scaling `delta_T^2 h_T^{d-2}` is the local `H1` energy associated with changing
a fixed number of Bernstein coefficients by `delta_T`.

## 6. Marking and refinement rule

1. Compute the unconstrained or current constrained degree-`p` solution.
2. Evaluate all local Bernstein coefficient violations.
3. On cells with significant `delta_T`, reconstruct the contact set from the local
   polynomial or obstacle multiplier.
4. If the reconstructed contact crosses the element interior, split or curve the
   element so that the contact becomes part of the local skeleton.
5. Otherwise apply standard Dörfler marking using the combined estimator.
6. Re-solve on the fitted/refined mesh.

The decisive marking test is

```text
delta_T > C_target h_T^p.
```

Such a cell cannot support degree-`p` accuracy without contact alignment or a
higher-order flatness mechanism.

## 7. Target adaptive theorem

Assume:

- residual reliability and local efficiency;
- stable transfer between successive coefficient cones;
- a contact reconstruction with Hausdorff error `O(h_T^{p+1})` on marked cells;
- fitted refinement preserving shape regularity;
- estimator reduction after contact fitting;
- discrete reliability and quasi-orthogonality for the variational inequality.

Then the adaptive sequence should satisfy

```text
||u-u_l||_{H1}
  <= C (#T_l-#T_0)^{-s}
```

for every approximation-class exponent `s` available to a contact-fitted
high-order mesh.

The novel component compared with standard obstacle AFEM is the contact-phase
reduction lemma:

```text
sum_{T in refined patch} delta_T(new)^2 h_T^{d-2}
 <= rho sum_{T in old patch} delta_T(old)^2 h_T^{d-2}
    + C eta_Gamma^2,
```

with `rho<1`, and with exact vanishing for pure polynomial contact after exact
alignment.

## 8. hp consequence

On a fixed phase-misaligned cell containing an interior quadratic zero, degree
increase alone does not make the exact quadratic coefficient-feasible.  At the
central coefficient the defect is

```text
gamma_p h^2,

gamma_p = 1/[4(p-1)]  for even p,
gamma_p = 1/(4p)      for odd p.
```

Thus the exact polynomial remains outside the cone for every finite `p`; the raw
coefficient defect decreases only algebraically in `p`.  Exponential hp convergence
at contact therefore requires geometry alignment, strict clearance, or a different
constraint representation.

## 9. Practical conclusion

The coefficient cone is not intrinsically low order.  It becomes low order when a
finite-order contact set cuts elements at a persistent interior phase.  A
contact-aware mesh converts the bad profile into a barycentric monomial with
nonnegative coefficients, after which high-order approximation can resume.
