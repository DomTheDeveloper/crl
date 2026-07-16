# WOWII Graph Conjecture 314

This directory contains the complete human proof and Lean 4 formalization of the exact theorem in
`FormalConjectures.WrittenOnTheWallII.GraphConjecture314`.

## Files

- `PROOF.md` — self-contained mathematical proof.
- `proof/WOWII/ZZGraphConjecture314Final.lean` — top-level exact theorem.
- `proof/WOWII/` — dependency-ordered structural and total-domination lemmas.
- `.github/workflows/audit-wowii314.yml` — clean-room compilation and axiom audit.

## Pinned environment

The audit uses Google DeepMind Formal Conjectures commit
`b2e608fc52d765510915a244bb69b1a2741acc3c` and its `lean-toolchain`
(`leanprover/lean4:v4.27.0`).

## Reproduce locally

From a clean checkout of the pinned Formal Conjectures repository:

```bash
mkdir -p WOWII
cp /path/to/crl/math/wowii/143/proof/WOWII/GraphConjecture143Proof.lean WOWII/
cp /path/to/crl/math/wowii/314/proof/WOWII/*.lean WOWII/
lake exe cache get
lake env lean WOWII/ZZGraphConjecture314Final.lean
```

For the exact type and axiom audit, create `WOWII/Audit314.lean`:

```lean
import FormalConjectures.WrittenOnTheWallII.GraphConjecture314
import WOWII.ZZGraphConjecture314Final

namespace WrittenOnTheWallII.GraphConjecture314
open Classical SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

example [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α,
      G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  exact conjecture314_proved G hG hTriFree hPath

#print axioms conjecture314_proved
end WrittenOnTheWallII.GraphConjecture314
```

Then run:

```bash
lake env lean WOWII/Audit314.lean
```

The repository workflow additionally rejects explicit `sorry`, `admit`, custom `axiom`,
`native_decide`, and `opaque` declarations, and fails if the transitive axiom printout contains
`sorryAx`.
