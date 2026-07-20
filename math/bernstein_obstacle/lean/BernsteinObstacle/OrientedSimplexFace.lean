import BernsteinObstacle.SimplexFace
import BernsteinObstacle.SimplexFaceField
import BernsteinObstacle.SimplexPermutation
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Arbitrarily oriented simplex faces

The standard last-face restriction is transported by an arbitrary equivalence
of the ambient barycentric-coordinate index set.  This supplies the concrete
orientation layer needed when neighboring simplices enumerate a common face in
different local orders.
-/

/-- Embed a face point into an arbitrarily oriented ambient face. -/
def orientedFacePoint (d : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (x : BarycentricPoint d) : BarycentricPoint (d + 1) :=
  permuteBarycentricPoint (d + 1) e (lastFacePoint d x)

/-- Embed a face multi-index into the same arbitrarily oriented ambient face. -/
def orientedFaceMultiIndex (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (β : MultiIndex d n) : MultiIndex (d + 1) n :=
  permuteMultiIndex (d + 1) n e (lastFaceMultiIndex d n β)

/-- Extend face coefficients by zero and transport them to an arbitrary
orientation of the ambient simplex. -/
def orientedFaceCoefficientExtension (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : MultiIndex d n → ℝ) : MultiIndex (d + 1) n → ℝ :=
  fun α => lastFaceCoefficientExtension d n c
    (permuteMultiIndex (d + 1) n e.symm α)

/-- An oriented face basis function restricts exactly to its
lower-dimensional Bernstein basis function. -/
theorem simplexBasis_orientedFace_embed (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (β : MultiIndex d n) (x : BarycentricPoint d) :
    simplexBasis (d + 1) n (orientedFaceMultiIndex d n e β)
        (orientedFacePoint d e x) =
      simplexBasis d n β x := by
  unfold orientedFaceMultiIndex orientedFacePoint
  rw [simplexBasis_permute]
  exact simplexBasis_lastFace_embed d n β x

/-- The whole zero-extended ambient Bernstein field restricts, in any local
orientation, to the original face field. -/
theorem simplexField_orientedFace_extension (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    simplexField (d + 1) n (orientedFaceCoefficientExtension d n e c)
        (orientedFacePoint d e x) =
      simplexField d n c x := by
  unfold orientedFaceCoefficientExtension orientedFacePoint
  rw [simplexField_permute]
  exact simplexField_lastFace_extension d n c x

end

end BernsteinObstacle
