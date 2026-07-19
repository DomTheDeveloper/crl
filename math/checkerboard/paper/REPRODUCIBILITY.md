# Reproducibility record: checkerboard `2n-4` theorem

## Exact theorem

For every `n >= 6`, every no-three-in-line subset of either checkerboard parity class of the `n x n` integer grid has cardinality at most `2n - 4`.

Lean declaration:

```lean
Checkerboard.checkerboard_upper_all_n
```

## Canonical source

- Repository: `DomTheDeveloper/crl`
- Clean proof branch: `proof/checkerboard-all-n-clean`
- Clean proof commit: `961e2faaf8747b4feda4b12742d6cfc8284291ba`
- Review PR: `#63`
- Lean toolchain: `leanprover/lean4:v4.32.0`

The proof-critical source blobs in the clean branch are byte-identical to those in the development branch that passed the focused audit.

## Passed focused audit

- Workflow run: `29664945600`
- Job: `88133689652`
- Platform: GitHub-hosted macOS ARM64
- Result: success

Passed gates:

1. reject unfinished proof markers and project-defined axioms;
2. resolve the pinned Mathlib dependency;
3. complete `lake build` and kernel checking;
4. import the package root and axiom-audit module;
5. reject `sorryAx` in the build/audit output.

## Axiom audit

`Checkerboard/AxiomAudit.lean` runs:

```lean
#print axioms Checkerboard.checkerboard_upper_all_n
```

The expected footprint is limited to standard foundational axioms used by Mathlib, such as `propext`, `Quot.sound`, and `Classical.choice`; `sorryAx` is forbidden.

## Independent finite checker

Run:

```bash
python3 verify_small_cases.py
```

It performs exact standard-library checks of:

- both `6 x 6` parity classes by enumerating all `C(18,9) = 48,620` nine-point subsets and checking rows, columns, and both slope-`+-1` diagonal families;
- the exceptional thin `7 x 7` integer line-cover certificate, including every point coverage and its exact cost.

## Full Lean replay

```bash
cd proofs/lean/Checkerboard
lake update
lake exe cache get
lake build
```

The package root imports `Checkerboard.AllNTheorem` and `Checkerboard.AxiomAudit`.

## Scope boundary

This package proves the finite upper bound `D_mono(n) <= 2n - 4` for every `n >= 6`. It does not prove exact values for all `n`, the four-direction asymptotic limit equality, or the true all-slope asymptotic lower bound.
