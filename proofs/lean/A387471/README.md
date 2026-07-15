# A387471 formalization

This project contains a proof manuscript and a Lean formalization campaign for OEIS A387471.

## Mathematical result

The proof manuscript derives

```text
a(n) = 6*n - 5                  when 5 does not divide n
a(n) = 6*n + 7                  when 5 divides n
```

from trigonometric Ceva and the published classification of minimal vanishing sums of six roots of unity. The relevant exceptional type `(R5:R3)` is known to determine the relation uniquely up to rotation.

## Kernel-checked Lean results

`A387471.lean` and `A387471Trig.lean` prove, without placeholders:

- the exact product-to-sum identity;
- equivalence of the concurrence equation with the reduced three-sine equation;
- the exact integer lattice reconstruction;
- reconstruction of the ordinary and two exceptional index families;
- the divisibility-by-five consequence for exceptional triples;
- the arithmetic closed form;
- transfer from the grid-level six-root classification to the index classification.

## Remaining formal work

The complete OEIS theorem is not yet inhabited in Lean. The remaining tasks are:

1. formalize the published weight-six vanishing-sum classification in Mathlib;
2. package the classified families as the exact finite set and prove its card.

See `PROOF.md` for the mathematical proof and the Lean files for the kernel-checked reductions.
