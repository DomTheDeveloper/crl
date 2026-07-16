# Generalization program after A317940

## Verified special case

The completed Lean proof treats

\[
\left(\prod_{r\ge0}(1+\tfrac12 z^{2^r})\right)^{1/2}.
\]

## General theorem

For real or rational parameters \(0<q\le1\) and \(\alpha>0\), define the formal series

\[
F_{q,\alpha}(z)=\prod_{r\ge0}(1+qz^{2^r})^\alpha.
\]

Then every coefficient of \(F_{q,\alpha}\) is strictly positive.

For \(n=2^vm\), \(m\) odd,

\[
[z^n]\log F_{q,\alpha}
=\frac{\alpha}{m}\left(q^m-\sum_{j=1}^{v}\frac{q^{2^jm}}{2^j}\right)>0.
\]

The inequality follows from \(q^{2^jm}\le q^m\) and the strict finite bound
\(\sum_{j=1}^{v}2^{-j}<1\).

## Formal verification of the parameterized positivity core

[`DigitalEulerPositivity.lean`](./DigitalEulerPositivity.lean) defines, for rational
`0 < q ≤ 1` and `α > 0`, the canonical coefficient sequence characterized by

\[
F'(z)=\alpha D_q(z)F(z),\qquad F(0)=1,
\]

where \(D_q\) is the logarithmic derivative determined by the binary Euler
product's functional equation. Lean proves:

1. every coefficient of \(D_q\) has the positive lower bound \(q^{n+1}\);
2. every coefficient of the canonical solution \(F\) is strictly positive;
3. the associated formal power series satisfies the defining differential equation.

This parameterized Lean file passed strict AXLE verification under Lean 4.27.0
with no errors, warnings, failed declarations, placeholders, or custom axioms.
The remaining general-formalization step is to package the identification of this
canonical ODE solution with the notation
\(\prod_{r\ge0}(1+qz^{2^r})^\alpha\) for arbitrary rational \(\alpha\).
That identification is already supplied mathematically by the formal logarithm,
but has not yet been encoded as a separate reusable Lean API theorem.

## Research questions

1. Determine the maximal parameter region in \((q,\alpha)\) for coefficientwise nonnegativity or positivity.
2. Replace the binary exponents \(2^r\) by \(b^r\) for integer bases \(b\ge2\).
3. Classify weight sequences \(w_r\) for which \(\prod_r(1+w_rz^{2^r})^\alpha\) has positive coefficients.
4. Translate these coefficient criteria into positivity theorems for Dirichlet roots of multiplicative functions.
5. Determine denominator and divisibility properties of the A317940 local coefficients.
6. Generalize the Lean theorem from `ℚ` to an appropriate ordered field.

## Strongest paper framing

The broader project is:

> A coefficient-positivity theorem for fractional powers of digital Euler products, with applications to Dirichlet roots of multiplicative functions and a Lean-verified resolution of OEIS A317940.

The A317940 specialization and the parameterized coefficient-positivity core are now formally verified. The arbitrary-parameter product notation and broader base-\(b\) extensions remain future formalization work.
