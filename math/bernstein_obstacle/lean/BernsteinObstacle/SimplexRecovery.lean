import BernsteinObstacle.SimplexOrientedFace
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Positive Bernstein sampling recovery on a simplex

For positive degree, every simplex multi-index determines its barycentric
lattice point `α / n`.  Sampling a nonnegative function at these points gives
nonnegative Bernstein coefficients and therefore a pointwise nonnegative
recovery field.  The lattice points commute exactly with face embeddings and
coordinate permutations, which is the concrete local conformity mechanism.
-/

/-- The barycentric lattice point associated with a degree-`n` multi-index. -/
def simplexLatticePoint (d n : ℕ) (hn : 0 < n)
    (α : MultiIndex d n) : BarycentricPoint d := by
  refine ⟨fun i => (α.1 i : ℝ) / (n : ℝ), ?_, ?_⟩
  · intro i
    exact div_nonneg (by positivity) (by positivity)
  · have hsum : (∑ i : Fin (d + 1), (α.1 i : ℝ)) = (n : ℝ) := by
      exact_mod_cast α.2
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hn)
    rw [← Finset.sum_div, hsum, div_self hnR]

@[simp]
theorem simplexLatticePoint_apply (d n : ℕ) (hn : 0 < n)
    (α : MultiIndex d n) (i : Fin (d + 1)) :
    (simplexLatticePoint d n hn α).1 i = (α.1 i : ℝ) / (n : ℝ) := by
  rfl

/-- Barycentric lattice points commute with coordinate permutations. -/
theorem simplexLatticePoint_permute (d n : ℕ) (hn : 0 < n)
    (e : Fin (d + 1) ≃ Fin (d + 1)) (α : MultiIndex d n) :
    simplexLatticePoint d n hn (permuteMultiIndex d n e α) =
      permuteBarycentricPoint d e (simplexLatticePoint d n hn α) := by
  apply Subtype.ext
  funext i
  rfl

/-- Barycentric lattice points commute with the standard last-face embedding. -/
theorem simplexLatticePoint_lastFaceMultiIndex (d n : ℕ) (hn : 0 < n)
    (β : MultiIndex d n) :
    simplexLatticePoint (d + 1) n hn (lastFaceMultiIndex d n β) =
      lastFacePoint d (simplexLatticePoint d n hn β) := by
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [simplexLatticePoint]
  · simp [simplexLatticePoint]

/-- Barycentric lattice points commute with every oriented face embedding. -/
theorem simplexLatticePoint_orientedLastFaceMultiIndex
    (d n : ℕ) (hn : 0 < n)
    (e : Fin (d + 2) ≃ Fin (d + 2)) (β : MultiIndex d n) :
    simplexLatticePoint (d + 1) n hn
        (orientedLastFaceMultiIndex d n e β) =
      orientedLastFacePoint d e (simplexLatticePoint d n hn β) := by
  unfold orientedLastFaceMultiIndex orientedLastFacePoint
  rw [simplexLatticePoint_permute,
    simplexLatticePoint_lastFaceMultiIndex]

/-- Bernstein coefficients obtained by sampling a function on the complete
barycentric degree-`n` lattice. -/
def simplexSamplingCoefficients (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint d → ℝ) : MultiIndex d n → ℝ :=
  fun α => w (simplexLatticePoint d n hn α)

/-- The corresponding simplex Bernstein sampling recovery field. -/
def simplexSamplingRecovery (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint d → ℝ) : BarycentricPoint d → ℝ :=
  simplexField d n (simplexSamplingCoefficients d n hn w)

/-- Sampling a nonnegative function gives nonnegative Bernstein coefficients. -/
theorem simplexSamplingCoefficients_nonneg
    (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint d → ℝ) (hw : ∀ x, 0 ≤ w x)
    (α : MultiIndex d n) :
    0 ≤ simplexSamplingCoefficients d n hn w α := by
  exact hw (simplexLatticePoint d n hn α)

/-- The positive sampling recovery is pointwise nonnegative throughout the
simplex. -/
theorem simplexSamplingRecovery_nonneg
    (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint d → ℝ) (hw : ∀ x, 0 ≤ w x)
    (x : BarycentricPoint d) :
    0 ≤ simplexSamplingRecovery d n hn w x := by
  exact simplexField_nonneg d n
    (simplexSamplingCoefficients d n hn w)
    (simplexSamplingCoefficients_nonneg d n hn w hw) x

/-- A sampled coefficient on the standard last face is exactly the function
value at the corresponding embedded face lattice point. -/
theorem simplexSamplingCoefficients_lastFace
    (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint (d + 1) → ℝ) (β : MultiIndex d n) :
    simplexSamplingCoefficients (d + 1) n hn w
        (lastFaceMultiIndex d n β) =
      w (lastFacePoint d (simplexLatticePoint d n hn β)) := by
  unfold simplexSamplingCoefficients
  rw [simplexLatticePoint_lastFaceMultiIndex]

/-- The same exact face-sampling identity holds under an arbitrary ambient
orientation permutation. -/
theorem simplexSamplingCoefficients_orientedLastFace
    (d n : ℕ) (hn : 0 < n)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (w : BarycentricPoint (d + 1) → ℝ) (β : MultiIndex d n) :
    simplexSamplingCoefficients (d + 1) n hn w
        (orientedLastFaceMultiIndex d n e β) =
      w (orientedLastFacePoint d e
        (simplexLatticePoint d n hn β)) := by
  unfold simplexSamplingCoefficients
  rw [simplexLatticePoint_orientedLastFaceMultiIndex]

/-- If a function vanishes on an oriented face, every sampled Bernstein
coefficient belonging to that face is exactly zero. -/
theorem simplexSamplingCoefficients_orientedBoundary_eq_zero
    (d n : ℕ) (hn : 0 < n)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (w : BarycentricPoint (d + 1) → ℝ)
    (hboundary : ∀ x : BarycentricPoint d,
      w (orientedLastFacePoint d e x) = 0)
    (β : MultiIndex d n) :
    simplexSamplingCoefficients (d + 1) n hn w
        (orientedLastFaceMultiIndex d n e β) = 0 := by
  rw [simplexSamplingCoefficients_orientedLastFace]
  exact hboundary (simplexLatticePoint d n hn β)

end

end BernsteinObstacle
