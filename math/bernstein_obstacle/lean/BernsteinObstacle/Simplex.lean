import BernsteinObstacle.Core
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-- A point of the standard `d`-simplex, represented by nonnegative barycentric
coordinates whose sum is one. -/
abbrev BarycentricPoint (d : ℕ) :=
  {coord : Fin (d + 1) → ℝ //
    (∀ i, 0 ≤ coord i) ∧ (∑ i, coord i) = 1}

/-- A degree-`n` multi-index on a `d`-simplex. Each component is automatically
bounded by `n`, and the component sum is exactly `n`. -/
abbrev MultiIndex (d n : ℕ) :=
  {α : Fin (d + 1) → Fin (n + 1) //
    ∑ i, (α i : ℕ) = n}

/-- The simplicial Bernstein basis weight associated with a multi-index. -/
def simplexBasis (d n : ℕ) (α : MultiIndex d n)
    (x : BarycentricPoint d) : ℝ :=
  ((Nat.factorial n : ℝ) /
      ∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ)) *
    ∏ i : Fin (d + 1), (x.1 i) ^ (α.1 i : ℕ)

/-- Every simplicial Bernstein basis weight is nonnegative on the standard simplex. -/
theorem simplexBasis_nonneg (d n : ℕ) (α : MultiIndex d n)
    (x : BarycentricPoint d) :
    0 ≤ simplexBasis d n α x := by
  unfold simplexBasis
  have hcoef :
      0 ≤ (Nat.factorial n : ℝ) /
        ∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ) := by
    positivity
  have hpowers :
      0 ≤ ∏ i : Fin (d + 1), (x.1 i) ^ (α.1 i : ℕ) := by
    apply Finset.prod_nonneg
    intro i hi
    exact pow_nonneg (x.2.1 i) _
  exact mul_nonneg hcoef hpowers

/-- A scalar polynomial represented in the degree-`n` simplicial Bernstein basis. -/
def simplexField (d n : ℕ) (c : MultiIndex d n → ℝ)
    (x : BarycentricPoint d) : ℝ :=
  ∑ α : MultiIndex d n, c α * simplexBasis d n α x

/-- Nonnegative simplicial Bernstein coefficients certify pointwise nonnegativity. -/
theorem simplexField_nonneg (d n : ℕ) (c : MultiIndex d n → ℝ)
    (hc : ∀ α, 0 ≤ c α) (x : BarycentricPoint d) :
    0 ≤ simplexField d n c x := by
  unfold simplexField
  exact Finset.sum_nonneg fun α _ =>
    mul_nonneg (hc α) (simplexBasis_nonneg d n α x)

/-- Coefficientwise clipping for a simplicial Bernstein polynomial. -/
def clipSimplex (d n : ℕ) (c : MultiIndex d n → ℝ) :
    MultiIndex d n → ℝ :=
  fun α => clip (c α)

/-- Clipping arbitrary simplicial coefficients yields a nonnegative polynomial. -/
theorem clipped_simplexField_nonneg (d n : ℕ)
    (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    0 ≤ simplexField d n (clipSimplex d n c) x := by
  exact simplexField_nonneg d n (clipSimplex d n c)
    (fun α => clip_nonneg (c α)) x

/-- An obstacle plus a simplicial Bernstein gap. -/
def simplexObstacleApprox (d n : ℕ)
    (ψ : BarycentricPoint d → ℝ) (c : MultiIndex d n → ℝ)
    (x : BarycentricPoint d) : ℝ :=
  ψ x + simplexField d n c x

/-- The simplicial bridge: finitely many nonnegative coefficients certify
pointwise no-penetration throughout the simplex. -/
theorem simplex_noPenetration_of_nonnegative_coefficients
    (d n : ℕ) (ψ : BarycentricPoint d → ℝ)
    (c : MultiIndex d n → ℝ) (hc : ∀ α, 0 ≤ c α)
    (x : BarycentricPoint d) :
    ψ x ≤ simplexObstacleApprox d n ψ c x := by
  unfold simplexObstacleApprox
  have hgap : 0 ≤ simplexField d n c x := simplexField_nonneg d n c hc x
  linarith

/-- Clipping arbitrary simplicial gap coefficients gives a certified
nonpenetrating approximation throughout the simplex. -/
theorem simplex_noPenetration_after_clipping
    (d n : ℕ) (ψ : BarycentricPoint d → ℝ)
    (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    ψ x ≤ simplexObstacleApprox d n ψ (clipSimplex d n c) x := by
  exact simplex_noPenetration_of_nonnegative_coefficients d n ψ
    (clipSimplex d n c) (fun α => clip_nonneg (c α)) x

end

end BernsteinObstacle
