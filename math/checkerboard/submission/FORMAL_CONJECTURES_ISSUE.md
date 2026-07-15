# Formal Conjectures issue draft

## Proposed title

Add Prellberg's checkerboard no-three-in-line conjectures

## Proposed body

### Source

Thomas Prellberg, *No-three-in-line sets on the checkerboard grid*, arXiv:2605.09215 (2026).

### Motivation

The repository currently contains the classical unrestricted no-three-in-line problem, but not the checkerboard-restricted problem or the three parity-sensitive four-direction linear-programming conjectures introduced by Prellberg.

The checkerboard paper gives unusually explicit finite LPs, an exact continuum obstacle certificate, and a concrete algebraic limiting constant, making the statements useful formalization targets.

### Proposed statements

I propose adding a source file such as

```text
FormalConjectures/Paper/PrellbergCheckerboard.lean
```

with clearly separated definitions and theorems for:

1. **Finite checkerboard bound**

   For every `n ≥ 6`, a monochromatic no-three-in-line subset of the `n × n` grid has cardinality at most `2n-4`.

2. **Four-direction LP limit**

   The normalized odd-fat, odd-thin and even four-direction LP optima converge to the middle real root

   ```text
   401 α^3 - 1744 α^2 + 2240 α - 768 = 0.
   ```

3. **Checkerboard NTIL limit**

   The normalized maximum size of a monochromatic all-slope no-three-in-line set converges to the same constant `α`.

### Research status

- The source paper states the limiting results as conjectures.
- A separate research repository contains a proof draft and exact certificates for the finite bound and the four-direction LP limit.
- The stronger all-slope checkerboard NTIL lower bound remains open.
- The available Lean code currently formalizes only the algebraic core and should not be described as a complete formal proof of statements 1 or 2.

### Relationship to Green 72

The proposed file is not a duplicate of `GreensOpenProblems/72.lean`. Green 72 concerns unrestricted all-slope NTIL sets on the full square grid. Prellberg's problem restricts points to one checkerboard parity class and introduces additional parity-sensitive LP structures.

### Attribution

The conjectures and continuum certificate should be attributed to Thomas Prellberg. Any follow-up proof submission should cite the source paper and clearly separate inherited definitions/certificates from new arguments.
