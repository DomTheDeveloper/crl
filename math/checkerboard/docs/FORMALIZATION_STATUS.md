# Lean formalization status for `D_mono(n) ≤ 2n - 4`

## Current verification state

The branch `solve/checkerboard-2n4-full` now contains Lean source for the exact
universal theorem

```lean
theorem Checkerboard.checkerboard_Dmono_le (n : ℕ) (hn : 6 ≤ n) :
    Dmono n ≤ 2 * n - 4
```

and an explicit

```lean
#print axioms Checkerboard.checkerboard_Dmono_le
```

The source dependency chain is complete on inspection, but the pinned GitHub
Actions jobs are currently queued and no successful `lake build` or axiom-audit
log has yet been produced for the current commit.  Therefore the theorem must
not yet be described as kernel-checked.

## Intended proof dependency chain

The following modules implement the finite proof:

1. `FiniteFramework.lean`
   - the finite board and checkerboard color predicate;
   - finite fibers and exact fiberwise double counting;
   - weighted Cauchy-Schwarz and elementary square-sum formulas.
2. `CapacityProfiles.lean`
   - endpoint and all-double diagonal capacity profiles;
   - exact capacity totals and centered second moments.
3. `ProfileLemmas.lean`
   - profile first moments;
   - exact diagonal-coordinate radius bounds.
4. `DeficitAlgebra.lean`
   - a natural deficit of total mass one is a unique unit mass;
   - equality of first-moment squares and second moments;
   - the scaled `q=1` master Cauchy lower bound.
5. `MomentBridge.lean`
   - row, column, and diagonal deficits defined from actual finite fibers;
   - exact deficit totals;
   - exact first- and second-moment bridge identities.
6. `Geometry.lean`
   - integer-affine-line no-three-in-line predicate;
   - inheritance under subsets;
   - row, column, and principal-diagonal line capacities;
   - checkerboard parity reindexing and concrete capacity profiles.
7. `ParityCases.lean`
   - odd endpoint/endpoint case;
   - odd all-double/all-double case;
   - both even mixed-profile cases;
   - the three strict terminal polynomial contradictions.
8. `FinalTheorem.lean`
   - arbitrary-cardinality reduction to exactly `2n-3` points;
   - colorwise extremal bound;
   - maximum over both checkerboard colors;
   - public theorem and axiom print.

The root `Checkerboard.lean` imports the complete chain.

## Source audit already performed

The branch has been checked statically for the following prohibited shortcuts:

- no source declaration of a custom `axiom` or `constant` in the checkerboard
  proof modules;
- no intended use of `sorry`, `admit`, or `native_decide`;
- no imported project theorem standing in for the universal argument;
- no finite computation used as the universal proof.

Two concrete Lean source defects found during audit were repaired:

1. singleton deficit sums were rewritten as explicit two-step calculations so
   `Finset.sum_eq_single_of_mem` has the unsimplified target it expects;
2. invalid `rw [...] at_mod_cast` syntax in the profile radius lemmas was
   replaced by explicit cast calculations with natural-subtraction side
   conditions.

These static checks are not a substitute for elaboration and kernel checking.

## Remaining formal verification gates

The formalization is complete only after all of the following succeed on the
current commit:

```bash
cd proofs/lean/Checkerboard
lake update
lake build
grep -RnE '\bsorry\b|\badmit\b|native_decide' --include='*.lean' .
lake env lean Checkerboard/FinalTheorem.lean
```

The final command must print an axiom list for
`Checkerboard.checkerboard_Dmono_le` containing no `sorryAx` or custom
mathematical axiom.  Standard Lean foundations such as `propext`,
`Classical.choice`, and `Quot.sound` are acceptable.

The project is pinned to Lean and Mathlib `v4.32.0`.

## Scope boundary

This exact finite theorem is separate from the checkerboard four-direction LP
asymptotic theorem and from the still-open all-slope asymptotic lower-bound
problem.  Neither asymptotic statement is imported by the finite proof.
