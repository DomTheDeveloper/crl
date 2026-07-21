# Transverse-prism saturation: remaining physical obligations

The formal theorem `transversePrism_localEnergy_lowerBound` isolates the
analytic content of the local-to-global lower-bound lift. To instantiate it on
a physical cut simplex `T`, the next geometry layer must prove exactly the
following facts.

1. **Embedded prism.** There is a measurable tangential cross-section `Y_T` and
   a family of normal segments of length `h_T` contained in `T`.
2. **Uniform cut phase.** On every retained segment, the free boundary crosses
   at a phase `theta_T` satisfying `eta <= theta_T <= 1 - eta`.
3. **Tangential mass.** The pushed-forward tangential measure satisfies
   `M * h_T^(d-1) <= μ_T.real Set.univ`, with `M > 0` independent of `T`.
4. **Quadratic restriction.** The normal derivative of every `P₂` polynomial on
   `T` restricts to an affine function `alpha y * x + beta y` on each segment.
5. **Jacobian/energy domination.** The physical local squared `H¹` error
   dominates the iterated transverse derivative error appearing in
   `transversePrism_localEnergy_lowerBound`, including the uniform lower bound
   on the change-of-variables Jacobian.

Once these five statements are supplied, the existing theorem yields

```text
C * h_T^(d+2) <= |u - v_h|_{H1(T)}^2
```

for every quadratic finite-element function on the cut element. No
coefficient-clipping assumption occurs in this lower-bound chain.
