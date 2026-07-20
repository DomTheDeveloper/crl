import BernsteinObstacle.Simplex
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Exact restriction to the standard last face

A point of a `d`-simplex embeds into the last codimension-one face of the
`(d+1)`-simplex by appending a zero barycentric coordinate.  Degree-`n`
face multi-indices embed the same way.  The corresponding ambient Bernstein
basis function restricts exactly to the lower-dimensional Bernstein basis,
while every ambient basis function having positive exponent in the omitted
coordinate vanishes identically on the face.
-/

/-- Embed a standard `d`-simplex point into the last face of the standard
`(d+1)`-simplex. -/
def lastFacePoint (d : ℕ) (x : BarycentricPoint d) :
    BarycentricPoint (d + 1) := by
  refine ⟨Fin.snoc x.1 0, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using x.2.1 j
  · rw [Fin.sum_univ_castSucc]
    simpa using x.2.2

/-- Embed a degree-`n` face multi-index into the last face of the ambient
`(d+1)`-simplex. -/
def lastFaceMultiIndex (d n : ℕ) (β : MultiIndex d n) :
    MultiIndex (d + 1) n := by
  refine ⟨Fin.snoc β.1 0, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simpa using β.2

@[simp]
theorem lastFacePoint_castSucc (d : ℕ) (x : BarycentricPoint d)
    (i : Fin (d + 1)) :
    (lastFacePoint d x).1 i.castSucc = x.1 i := by
  rfl

@[simp]
theorem lastFacePoint_last (d : ℕ) (x : BarycentricPoint d) :
    (lastFacePoint d x).1 (Fin.last (d + 1)) = 0 := by
  rfl

@[simp]
theorem lastFaceMultiIndex_castSucc (d n : ℕ) (β : MultiIndex d n)
    (i : Fin (d + 1)) :
    (lastFaceMultiIndex d n β).1 i.castSucc = β.1 i := by
  rfl

@[simp]
theorem lastFaceMultiIndex_last (d n : ℕ) (β : MultiIndex d n) :
    (lastFaceMultiIndex d n β).1 (Fin.last (d + 1)) = 0 := by
  rfl

/-- The ambient Bernstein basis associated with an embedded face multi-index
restricts exactly to the lower-dimensional Bernstein basis. -/
theorem simplexBasis_lastFace_embed (d n : ℕ)
    (β : MultiIndex d n) (x : BarycentricPoint d) :
    simplexBasis (d + 1) n (lastFaceMultiIndex d n β)
      (lastFacePoint d x) = simplexBasis d n β x := by
  unfold simplexBasis
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp

/-- Every ambient Bernstein basis function with positive exponent in the
omitted last coordinate vanishes identically on the last face. -/
theorem simplexBasis_lastFace_eq_zero_of_last_pos (d n : ℕ)
    (α : MultiIndex (d + 1) n) (x : BarycentricPoint d)
    (hpos : 0 < (α.1 (Fin.last (d + 1)) : ℕ)) :
    simplexBasis (d + 1) n α (lastFacePoint d x) = 0 := by
  unfold simplexBasis
  rw [Fin.prod_univ_castSucc]
  simp [zero_pow hpos]

end

end BernsteinObstacle
