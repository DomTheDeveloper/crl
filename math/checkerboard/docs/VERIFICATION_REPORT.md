# Checkerboard verification report

## Executive summary

This repository contains a research-draft proof and verification package for checkerboard no-three-in-line bounds and four-direction asymptotics. The evidence is intentionally divided into three levels:

1. **Lean-checked algebra:** exact identities and terminal inequalities;
2. **independently executable certificates:** Python, symbolic algebra, SAT/SMT and optimization checks;
3. **paper-level arguments:** finite-sum derivations, continuum measure transfer and hypergraph rounding.

The full all-slope checkerboard NTIL lower bound remains open.

## Claim matrix

| Claim | Mathematical proof | Exact computation | Lean status |
|---|---:|---:|---:|
| cubic relation `α=2(1-p)` | yes | yes | complete |
| terminal parity contradictions for `2n-4` | yes | yes | complete |
| full master defect-moment identity | yes, draft | extensive finite checks | not complete |
| `Dmono(n) ≤ 2n-4`, `n≥6` | yes, draft | SAT/SMT/MIP corroboration | algebraic end only |
| `Dmono(n) ≤ ceil(2^(2/3)n)` | yes, draft | symbolic checker | algebraic end only |
| exact continuum primal mass `α` | yes, certificate-assisted | two exact algebra implementations | not formalized |
| finite four-direction LP limit `α` | yes, draft | exact finite checks | not formalized |
| integral four-direction limit `α` | yes, draft using Kahn | finite sanity checks | not formalized |
| all-slope checkerboard NTIL limit `α` | **open** | exploratory only | none |

## Lean files

The Lean project under `proofs/lean/Checkerboard` contains no `sorry`, `admit`, or custom axioms. It checks:

- `Checkerboard/CubicTransform.lean`;
- `Checkerboard/MasterAlgebra.lean`;
- `Checkerboard/FiniteContradictions.lean`;
- `Checkerboard/CeilingAlgebra.lean`.

A clean build does **not** mean that the complete checkerboard theorem has been formalized. See `FORMALIZATION_STATUS.md`.

## Independent computational checks represented by the research bundle

The larger local research bundle associated with this project contains:

- exact reconstruction of the three parity-dependent capacity constants;
- randomized and exhaustive tests of the master identity;
- Z3 and CVC5 symbolic contradiction checks;
- SAT encodings for forbidden finite target sizes;
- HiGHS linear and mixed-integer optimization checks;
- exact arithmetic verification of the continuum transport weights;
- independent SymPy quotient-ring verification;
- exact rational all-line finite certificates for selected board sizes.

Binary reports and large certificate bundles should be attached to a tagged GitHub release rather than represented as Lean-verified source.

## Reproduction

```bash
cd proofs/lean/Checkerboard
lake update
lake build
```

The CI workflow also performs a source guard:

```bash
! grep -RnE '\bsorry\b|\badmit\b|native_decide' .
```

## Required review before publication

Before public claims of resolution, the following should be reviewed independently:

1. the parity-capacity profile derivation;
2. the complete finite moment identity;
3. the capacity-majorization lemma;
4. the support and projection interpretation of every continuum transport component;
5. the smoothing and finite-sampling lower transfer;
6. the exact statement of Kahn's theorem and every hypothesis in the blow-up construction.

## Safe public wording

> The repository contains a research-draft resolution of Prellberg's four-direction LP limit conjecture, new finite defect-moment bounds, extensive exact computational verification, and a partial sorry-free Lean formalization of the algebraic core. The full all-slope checkerboard no-three-in-line limit remains open.
