# Bernstein–Bézier obstacle grand theorem

## Grand statement

Let `E` be the ambient real Sobolev/Hilbert space. Let `K_h^B` be a moving
family of conforming Bernstein–Bézier coefficient cones and let `K` be the
continuous nonnegative cone. Assume the threshold-form recovery data required
by `ThresholdSobolevFEMRecoveryData`:

1. every `v in K` has a strongly convergent positive smooth approximation;
2. for every smooth approximation level, all sufficiently fine meshes admit a
   feasible positive Bernstein recovery;
3. that recovery is eventually within `1/(m+1)` in the ambient norm;
4. `K_h^B` is contained in `K`;
5. `K` is norm closed and convex.

Let discrete obstacles `psi_h` converge strongly to a continuous obstacle
`psi`. Define the relative Bernstein cones

```text
K_h^B(psi_h) = {u_h : u_h - psi_h in K_h^B}
K(psi)       = {u   : u   - psi   in K}.
```

Then

```text
K_h^B(psi_h)  --Mosco-->  K(psi).
```

Consequently, whenever the symmetric coercive variational-inequality/energy
argument supplies a vanishing solution-to-recovery bound, the corresponding
discrete minimizers converge strongly to the continuous minimizer.

## Grand rate law: consistency-saturation regime

Let:

- `s` be the obstacle-approximation order;
- `r` be the bulk finite-element approximation order;
- `m` be the coefficient-consistency order;
- `q` be the physical vanishing order of the gap at the defect/free boundary;
- `c` be the codimension of that defect set;
- `hGamma` be the local interface scale.

Assume the **consistency-saturation condition**

```text
q <= m.
```

In this regime the coefficient consistency is high enough to resolve the
physical vanishing order on the same interface scale. If the squared energy
error satisfies

```text
alpha * e_h^2
  <= P * h^(2s)
   + A * h^(2r)
   + B * hGamma^(2*(q-1)+c),
```

then

```text
e_h <= C * (
    h^s
  + h^r
  + hGamma^(q-1) * sqrt(hGamma^c)
).
```

The Lean theorem writes the final term as

```text
consistencyVanishingCodimensionScale hGamma m q c
```

and proves that it equals the physical vanishing-order/codimension scale under
`q <= m`.

## The unresolved sub-saturation regime

When

```text
m < q,
```

one must not simply replace `q` by `min(m,q)` while retaining the same interface
scale. The coefficient error becomes competitive with the physical gap farther
from the interface, and the risky layer has thickness of order

```text
h^(m/q).
```

The corresponding rate involves real/rational powers and a separately derived
geometric patch-count estimate. The current terminal Lean grand theorem does
not disguise this regime as a natural-power identity. Formalizing that
real-power sub-saturation theorem is a genuine next extension.

## Quadratic-contact saturation

For regular quadratic contact, `q = 2`. Across a codimension-one interface,
`c = 1`. Once `m >= 2`, the consistency-saturation hypothesis holds and the
interface term is exactly

```text
hGamma * sqrt(hGamma) = hGamma^(3/2).
```

Thus higher bulk polynomial degree can improve `h^r`, but it cannot improve the
unfitted positive-basis clipping exponent beyond `3/2` unless the physical
vanishing order, mesh/interface alignment, or repair mechanism changes.

## What is genuinely new in the grand formulation

1. **Moving nonzero obstacles.** The zero-obstacle theorem is promoted to
   strongly approximated moving obstacles by proving translation stability of
   sequential Mosco convergence.
2. **No exact-obstacle requirement at the abstract level.** Obstacle
   approximation contributes an explicit `h^s` term.
3. **Arbitrary defect codimension.** The repair law is indexed by `c`, not tied
   only to hypersurfaces.
4. **Arbitrary physical vanishing order in the saturation regime.** The repair
   law is indexed by `q` whenever `q <= m`.
5. **A rigorous saturation barrier.** Quadratic contact remains limited by the
   codimension-one `3/2` interface exponent once consistency reaches order two.
6. **A newly isolated frontier.** The sub-saturation case `m < q` is identified
   as a different real-power geometric regime rather than being folded into an
   unjustified `min(m,q)` formula.
7. **One terminal theorem.** Mosco convergence, strong minimizer convergence,
   and the generalized saturation-regime rate are packaged in
   `bernsteinBezierObstacleGrandTheorem`, with a quadratic-contact
   specialization.

## Lean files

- `TranslatedMosco.lean`
- `MovingObstacleConvergence.lean`
- `MovingObstacleRate.lean`
- `MinkowskiRate.lean`
- `MinkowskiSaturation.lean`
- `GrandSaturationRate.lean`
- `GrandTheorem.lean`
- `GrandTheoremAudit.lean`

## Trust boundary

The grand theorem is an abstract formal theorem once the supplied data and
energy inequalities are instantiated. It does **not** by itself formalize or
independently validate:

- the concrete `H_0^1(Omega)` construction;
- positive smooth density in the physical cone;
- a complete moving conforming simplicial mesh object;
- affine pullback and physical Bernstein sampling estimates;
- the local free-boundary geometry and multiplier estimates that produce the
  energy bound;
- the real-power sub-saturation theorem for `m < q`;
- external novelty or correctness review.

For a physical nonzero obstacle, `psi_h` must be an admissible discrete obstacle
and the coefficient constraint must be imposed on `u_h - psi_h`. Strong
convergence of `psi_h` proves Mosco transfer, while a sharp rate additionally
requires the displayed obstacle-consistency energy term.

No theorem should be described as kernel verified until the pinned Lean build
and `#print axioms` audit for the exact commit succeed.
