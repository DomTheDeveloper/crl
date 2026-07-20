import BernsteinObstacle.Simplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Affine coordinates for simplex lattice indices

A degree-`n` simplex multi-index has `d + 1` nonnegative coordinates summing to
`n`.  The first `d` coordinates are free subject only to having sum at most
`n`; the final coordinate is forced to be the complementary value.  This file
packages that correspondence as an explicit equivalence.
-/

/-- The `d` independent coordinates of a degree-`n` simplex lattice point. -/
abbrev AffineMultiIndex (d n : ℕ) :=
  {γ : Fin d → Fin (n + 1) // ∑ i, (γ i : ℕ) ≤ n}

/-- Forget the final, dependent barycentric lattice coordinate. -/
def multiIndexToAffine (d n : ℕ) (α : MultiIndex d n) :
    AffineMultiIndex d n := by
  refine ⟨fun i => α.1 i.castSucc, ?_⟩
  change (∑ i : Fin d, (α.1 i.castSucc : ℕ)) ≤ n
  have hsum := α.2
  rw [Fin.sum_univ_castSucc] at hsum
  omega

/-- Recover the full simplex multi-index by adjoining the complementary final
coordinate. -/
def affineToMultiIndex (d n : ℕ) (γ : AffineMultiIndex d n) :
    MultiIndex d n := by
  let s : ℕ := ∑ i, (γ.1 i : ℕ)
  let lastCoord : Fin (n + 1) :=
    ⟨n - s, Nat.lt_succ_iff.mpr (Nat.sub_le n s)⟩
  refine ⟨Fin.snoc γ.1 lastCoord, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change (∑ i, (γ.1 i : ℕ)) + (n - ∑ i, (γ.1 i : ℕ)) = n
  omega

@[simp]
theorem multiIndexToAffine_affineToMultiIndex (d n : ℕ)
    (γ : AffineMultiIndex d n) :
    multiIndexToAffine d n (affineToMultiIndex d n γ) = γ := by
  apply Subtype.ext
  funext i
  simp [multiIndexToAffine, affineToMultiIndex]

@[simp]
theorem affineToMultiIndex_multiIndexToAffine (d n : ℕ)
    (α : MultiIndex d n) :
    affineToMultiIndex d n (multiIndexToAffine d n α) = α := by
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply Fin.ext
    change n - (∑ j : Fin d, (α.1 j.castSucc : ℕ)) =
      (α.1 (Fin.last d) : ℕ)
    have hsum := α.2
    rw [Fin.sum_univ_castSucc] at hsum
    omega
  · simp [affineToMultiIndex, multiIndexToAffine]

/-- Full degree-`n` simplex lattice indices are equivalent to their `d`
independent affine coordinates. -/
def multiIndexAffineEquiv (d n : ℕ) :
    MultiIndex d n ≃ AffineMultiIndex d n where
  toFun := multiIndexToAffine d n
  invFun := affineToMultiIndex d n
  left_inv := affineToMultiIndex_multiIndexToAffine d n
  right_inv := multiIndexToAffine_affineToMultiIndex d n

end

end BernsteinObstacle
