import BernsteinObstacle.SimplexFace
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Complete Bernstein fields on the standard last face

Face coefficients extend to ambient coefficients by placing them on the
embedded face multi-indices and setting every off-face coefficient to zero.
The complete ambient Bernstein field then restricts exactly to the original
lower-dimensional face field.
-/

/-- The embedding of face multi-indices into ambient multi-indices is
injective. -/
theorem lastFaceMultiIndex_injective (d n : ℕ) :
    Function.Injective (lastFaceMultiIndex d n) := by
  intro β γ h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := congrArg
    (fun α : MultiIndex (d + 1) n => (α.1 i.castSucc : ℕ)) h
  simpa using hi

/-- Extend face coefficients to the ambient simplex by zero outside the
embedded face multi-indices. -/
def lastFaceCoefficientExtension (d n : ℕ)
    (c : MultiIndex d n → ℝ) : MultiIndex (d + 1) n → ℝ :=
  fun α =>
    ∑ β : MultiIndex d n,
      if lastFaceMultiIndex d n β = α then c β else 0

/-- The zero extension recovers the original coefficient at every embedded
face multi-index. -/
theorem lastFaceCoefficientExtension_embed (d n : ℕ)
    (c : MultiIndex d n → ℝ) (β : MultiIndex d n) :
    lastFaceCoefficientExtension d n c (lastFaceMultiIndex d n β) = c β := by
  classical
  unfold lastFaceCoefficientExtension
  rw [Finset.sum_eq_single β]
  · simp
  · intro γ hγ hne
    have himage : lastFaceMultiIndex d n γ ≠ lastFaceMultiIndex d n β := by
      intro h
      exact hne ((lastFaceMultiIndex_injective d n) h)
    simp [himage]
  · intro hnot
    exact (hnot (Finset.mem_univ β)).elim

/-- The zero extension vanishes on every ambient multi-index having positive
exponent in the omitted coordinate. -/
theorem lastFaceCoefficientExtension_eq_zero_of_last_pos (d n : ℕ)
    (c : MultiIndex d n → ℝ) (α : MultiIndex (d + 1) n)
    (hpos : 0 < (α.1 (Fin.last (d + 1)) : ℕ)) :
    lastFaceCoefficientExtension d n c α = 0 := by
  classical
  unfold lastFaceCoefficientExtension
  apply Finset.sum_eq_zero
  intro β hβ
  have hne : lastFaceMultiIndex d n β ≠ α := by
    intro h
    have hlast := congrArg
      (fun γ : MultiIndex (d + 1) n =>
        (γ.1 (Fin.last (d + 1)) : ℕ)) h
    simp at hlast
    omega
  simp [hne]

/-- Extending face coefficients by zero and evaluating the ambient field on
the face gives exactly the lower-dimensional Bernstein field. -/
theorem simplexField_lastFace_extension (d n : ℕ)
    (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    simplexField (d + 1) n (lastFaceCoefficientExtension d n c)
        (lastFacePoint d x) =
      simplexField d n c x := by
  classical
  unfold simplexField lastFaceCoefficientExtension
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [Finset.sum_eq_single (lastFaceMultiIndex d n β)]
  · simp [simplexBasis_lastFace_embed]
  · intro α hα hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ (lastFaceMultiIndex d n β))).elim

end

end BernsteinObstacle
