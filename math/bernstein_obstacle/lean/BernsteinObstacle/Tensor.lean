import BernsteinObstacle.Core

open scoped BigOperators

namespace BernsteinObstacle

/-- A three-dimensional tensor-product Bernstein basis function. -/
def basis3 (n i j k : ℕ) (x y z : ℝ) : ℝ :=
  basis n i x * basis n j y * basis n k z

/-- Tensor-product Bernstein basis functions are nonnegative on the unit cube. -/
theorem basis3_nonneg (n i j k : ℕ)
    {x y z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ basis3 n i j k x y z := by
  unfold basis3
  exact mul_nonneg
    (mul_nonneg (basis_nonneg n i hx0 hx1) (basis_nonneg n j hy0 hy1))
    (basis_nonneg n k hz0 hz1)

/-- A scalar field represented in a degree-`n` tensor-product Bernstein basis. -/
def field3 (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ) (x y z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (n + 1), c i j k * basis3 n i j k x y z

/-- Nonnegative tensor-product coefficients certify pointwise nonnegativity on the unit cube. -/
theorem field3_nonneg (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (n + 1),
        ∀ k ∈ Finset.range (n + 1), 0 ≤ c i j k)
    {x y z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ field3 n c x y z := by
  unfold field3
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hc i hi j hj k hk)
    (basis3_nonneg n i j k hx0 hx1 hy0 hy1 hz0 hz1)

/-- Coefficientwise clipping of a three-dimensional Bernstein field. -/
def clip3 (c : ℕ → ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ :=
  fun i j k => clip (c i j k)

/-- Clipping arbitrary tensor-product coefficients yields a nonnegative field. -/
theorem clipped_field3_nonneg (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ)
    {x y z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ field3 n (clip3 c) x y z := by
  apply field3_nonneg n (clip3 c)
  intro i hi j hj k hk
  exact clip_nonneg (c i j k)

/-- An obstacle plus a three-dimensional tensor-product Bernstein gap. -/
def obstacleApprox3
    (ψ : ℝ → ℝ → ℝ → ℝ) (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ)
    (x y z : ℝ) : ℝ :=
  ψ x y z + field3 n c x y z

/-- Downstream 3D theorem: finitely many nonnegative coefficients certify no penetration. -/
theorem noPenetration3_of_nonnegative_coefficients
    (ψ : ℝ → ℝ → ℝ → ℝ) (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (n + 1),
        ∀ k ∈ Finset.range (n + 1), 0 ≤ c i j k)
    {x y z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ψ x y z ≤ obstacleApprox3 ψ n c x y z := by
  unfold obstacleApprox3
  have hgap : 0 ≤ field3 n c x y z :=
    field3_nonneg n c hc hx0 hx1 hy0 hy1 hz0 hz1
  linarith

/-- Clipping arbitrary 3D gap coefficients gives a certified nonpenetrating field. -/
theorem noPenetration3_after_clipping
    (ψ : ℝ → ℝ → ℝ → ℝ) (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ)
    {x y z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ψ x y z ≤ obstacleApprox3 ψ n (clip3 c) x y z := by
  exact noPenetration3_of_nonnegative_coefficients ψ n (clip3 c)
    (fun i _ j _ k _ => clip_nonneg (c i j k))
    hx0 hx1 hy0 hy1 hz0 hz1

end BernsteinObstacle
