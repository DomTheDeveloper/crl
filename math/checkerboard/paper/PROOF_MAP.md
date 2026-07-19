# Paper-to-Lean proof map

## Public theorem

Paper: Theorem 1.1, `D_mono(n, epsilon) <= 2n - 4` for every `n >= 6`.

Lean:

```lean
Checkerboard.checkerboard_upper_all_n
```

Source: `proofs/lean/Checkerboard/Checkerboard/AllNTheorem.lean`.

## Model and all-slope semantics

- `Point n := Fin n x Fin n`
- `InColor`
- `Monochromatic`
- integer `determinant`
- `NoThreeInLine`

Source: `Checkerboard/Model.lean`.

The four principal line capacities are derived from `NoThreeInLine`; they are not substituted for the full determinant definition.

## Weighted line-cover lemma

Paper: Lemma 2.1.

Lean:

```lean
card_le_of_fourCertificate
```

Source: `Checkerboard/FourCertificate.lean`.

## Quadratic weights and coverage

Paper: master identity and Sections 3-4.

Lean:

```lean
oddQuadraticWeights
evenQuadraticWeights
oddQuadratic_nonnegative
evenQuadratic_nonnegative
oddQuadratic_coverage
evenQuadratic_coverage
```

Source: `Checkerboard/QuadraticWeights.lean`.

## Exact line sums and costs

Paper: equations for `A_m`, `F_m`, `T_m`, `A'_m`, `D'_m`, and all three certificate costs.

Lean:

```lean
oddQuadratic_cost_zero
oddQuadratic_cost_one
evenQuadratic_cost_zero
evenQuadratic_cost_one
```

Sources:

- `Checkerboard/FinPolynomialSums.lean`
- `Checkerboard/QuadraticCosts.lean`

## Uniform large-board bounds

Paper: odd fat for `m >= 3`, odd thin for `m >= 4`, even for `m >= 4`.

Lean:

```lean
odd_zero_upper
odd_one_upper
even_upper
```

Source: `Checkerboard/AllNUpper.lean`.

## Exceptional thin `7 x 7` case

Paper: integer line cover of cost 32 and minimum point coverage 3.

Lean:

```lean
n7ThinWeights
n7_one_upper
```

Source: `Checkerboard/AllNUpper.lean`.

## The two `6 x 6` cases

Paper: finite rejection of every nine-point subset under the four principal line capacities.

Lean:

```lean
n6p0_boolean_bound
n6p1_boolean_bound
n6_zero_upper
n6_one_upper
```

Source: `Checkerboard/N6Base.lean`.

## Final assembly and audit

Lean:

```lean
checkerboard_upper_from_seven
checkerboard_upper_all_n
#print axioms Checkerboard.checkerboard_upper_all_n
```

Sources:

- `Checkerboard/AllNUpper.lean`
- `Checkerboard/AllNTheorem.lean`
- `Checkerboard/AxiomAudit.lean`
