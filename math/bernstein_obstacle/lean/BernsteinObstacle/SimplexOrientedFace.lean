import BernsteinObstacle.SimplexFaceField
import BernsteinObstacle.SimplexPermutation
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Orientation-independent simplex face restriction

The standard last-face restriction theorem is transported through an arbitrary
permutation of the ambient barycentric coordinates.  This gives a concrete
polynomial realization of an oriented simplex face and proves equality of the
complete restricted Bernstein field, not merely equality of coefficient sums.
-/

/-- Embed a face point into an arbitrarily oriented ambient face. -/
def orientedLastFacePoint (d : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (x : BarycentricPoint d) : BarycentricPoint (d + 1) :=
  permuteBarycentricPoint (d + 1) e (lastFacePoint d x)

/-- Embed a face multi-index into an arbitrarily oriented ambient face. -/
def orientedLastFaceMultiIndex (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (β : MultiIndex d n) : MultiIndex (d + 1) n :=
  permuteMultiIndex (d + 1) n e (lastFaceMultiIndex d n β)

/-- Extend face coefficients by zero after transporting the standard last face
through an ambient coordinate permutation. -/
def orientedLastFaceCoefficientExtension (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : MultiIndex d n → ℝ) : MultiIndex (d + 1) n → ℝ :=
  fun α => lastFaceCoefficientExtension d n c
    (permuteMultiIndex (d + 1) n e.symm α)

/-- The oriented face-index embedding is injective. -/
theorem orientedLastFaceMultiIndex_injective (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2)) :
    Function.Injective (orientedLastFaceMultiIndex d n e) := by
  intro β γ h
  have hinv := congrArg (permuteMultiIndex (d + 1) n e.symm) h
  have hbase :
      lastFaceMultiIndex d n β = lastFaceMultiIndex d n γ := by
    simpa [orientedLastFaceMultiIndex, permuteMultiIndex_trans] using hinv
  exact (lastFaceMultiIndex_injective d n) hbase

/-- The oriented zero extension recovers every face coefficient. -/
@[simp]
theorem orientedLastFaceCoefficientExtension_embed (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : MultiIndex d n → ℝ) (β : MultiIndex d n) :
    orientedLastFaceCoefficientExtension d n e c
      (orientedLastFaceMultiIndex d n e β) = c β := by
  simp [orientedLastFaceCoefficientExtension, orientedLastFaceMultiIndex,
    lastFaceCoefficientExtension_embed]

/-- The oriented extension vanishes when the pulled-back ambient index has
positive exponent in the omitted standard coordinate. -/
theorem orientedLastFaceCoefficientExtension_eq_zero_of_offFace
    (d n : ℕ) (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : MultiIndex d n → ℝ) (α : MultiIndex (d + 1) n)
    (hpos : 0 < ((permuteMultiIndex (d + 1) n e.symm α).1
      (Fin.last (d + 1)) : ℕ)) :
    orientedLastFaceCoefficientExtension d n e c α = 0 := by
  exact lastFaceCoefficientExtension_eq_zero_of_last_pos d n c
    (permuteMultiIndex (d + 1) n e.symm α) hpos

/-- An oriented ambient Bernstein basis function restricts exactly to the
corresponding lower-dimensional Bernstein basis function. -/
theorem simplexBasis_orientedLastFace_embed (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (β : MultiIndex d n) (x : BarycentricPoint d) :
    simplexBasis (d + 1) n (orientedLastFaceMultiIndex d n e β)
        (orientedLastFacePoint d e x) =
      simplexBasis d n β x := by
  unfold orientedLastFaceMultiIndex orientedLastFacePoint
  rw [simplexBasis_permute, simplexBasis_lastFace_embed]

/-- The complete oriented ambient field restricts exactly to the original face
field.  This is the concrete orientation-independent conformity identity. -/
theorem simplexField_orientedLastFace_extension (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    simplexField (d + 1) n
        (orientedLastFaceCoefficientExtension d n e c)
        (orientedLastFacePoint d e x) =
      simplexField d n c x := by
  unfold orientedLastFaceCoefficientExtension orientedLastFacePoint
  calc
    simplexField (d + 1) n
        (fun α => lastFaceCoefficientExtension d n c
          (permuteMultiIndex (d + 1) n e.symm α))
        (permuteBarycentricPoint (d + 1) e (lastFacePoint d x)) =
      simplexField (d + 1) n (lastFaceCoefficientExtension d n c)
        (lastFacePoint d x) :=
      simplexField_permute (d + 1) n e
        (lastFaceCoefficientExtension d n c) (lastFacePoint d x)
    _ = simplexField d n c x := simplexField_lastFace_extension d n c x

end

end BernsteinObstacle
