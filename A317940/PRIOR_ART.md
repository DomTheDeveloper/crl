# Prior-art boundary for the A317940 proof

## What is already known

The digit-sum generating-product identity is part of the existing literature. In particular, Maxwell Schneider and Robert Schneider, *Digit sums and generating functions* (2018), give a general base-`B` product identity for generating functions weighted by base-`B` digits. In base two, this includes

\[
\sum_{n\ge0} q^{s_2(n)}z^n
=\prod_{r\ge0}(1+qz^{2^r}).
\]

Thus the product representation used in the A317940 argument should not be claimed as new.

## What targeted searches did not locate

Targeted searches by sequence identifier, exact theorem name, Dirichlet square-root language, binary digit-sum products, Mahler functions, and fractional powers did not locate:

1. a prior proof that the rational function underlying OEIS A317940 is nonnegative or strictly positive;
2. a proof that every coefficient of
   \[
   \prod_{r\ge0}(1+qz^{2^r})^\alpha
   \]
   is strictly positive throughout `0 < q ≤ 1`, `α > 0`;
3. the application of that coefficient theorem to positivity of a Dirichlet square root of A046644.

This is evidence, not a guarantee of priority. Differently worded, unpublished, non-indexed, or private prior work may exist.

## Responsible novelty claim

The appropriate current wording is:

> We give an apparently new positivity argument for a known binary digit-sum Euler product, yielding a Lean-verified resolution of the publicly open A317940 nonnegativity conjecture and suggesting a broader fractional-power positivity theorem.

Do not claim that the base product identity or the digit-sum generating function itself is new.
