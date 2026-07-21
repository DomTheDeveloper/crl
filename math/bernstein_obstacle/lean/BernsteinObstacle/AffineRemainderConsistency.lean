import BernsteinObstacle.SimplexSamplingAffine
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Quantitative consistency from affine cancellation

A convexly weighted operator that reproduces an affine model inherits the
uniform remainder bound between the target data and that affine model.  Applied
to simplex Bernstein sampling, this is the dimension-safe Taylor-cancellation
step behind the local `O(h^2)` estimate.
-/

/-- A finite convex combination inherits a uniform error bound whenever its
affine comparison combination equals the target value. -/
theorem abs_weighted_sum_sub_target_le
    {I : Type*} [Fintype I]
    (weight approx affine : I → ℝ) (target eps : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i : I, weight i) = 1)
    (haffine : (∑ i : I, weight i * affine i) = target)
    (heps : 0 ≤ eps)
    (hremainder : ∀ i, |approx i - affine i| ≤ eps) :
    |(∑ i : I, weight i * approx i) - target| ≤ eps := by
  calc
    |(∑ i : I, weight i * approx i) - target| =
        |(∑ i : I, weight i * approx i) -
          ∑ i : I, weight i * affine i| := by rw [haffine]
    _ = |∑ i : I, weight i * (approx i - affine i)| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i : I, |weight i * (approx i - affine i)| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ i : I, weight i * |approx i - affine i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hweight i)]
    _ ≤ ∑ i : I, weight i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hremainder i) (hweight i)
    _ = eps := by
      rw [← Finset.sum_mul, hsum, one_mul]

/-- The complete bounded-index simplicial Bernstein basis is a partition of
unity. -/
theorem simplexBasis_sum_eq_one
    (d n : ℕ) (x : BarycentricPoint d) :
    (∑ α : MultiIndex d n, simplexBasis d n α x) = 1 := by
  have hfield := simplexField_eq_simplexFieldNat_naturalize
    d n (fun _ : MultiIndex d n => 1) x
  have hnatural :
      simplexFieldNat d n
        (naturalizeSimplexCoefficients d n
          (fun _ : MultiIndex d n => 1)) x = 1 := by
    unfold simplexFieldNat
    calc
      (∑ α ∈ Finset.piAntidiag
          (Finset.univ : Finset (Fin (d + 1))) n,
        naturalizeSimplexCoefficients d n
            (fun _ : MultiIndex d n => 1) α *
          simplexBasisNat d n α x) =
        ∑ α ∈ Finset.piAntidiag
          (Finset.univ : Finset (Fin (d + 1))) n,
          simplexBasisNat d n α x := by
            apply Finset.sum_congr rfl
            intro α hα
            simp [naturalizeSimplexCoefficients, hα]
      _ = 1 := simplexBasisNat_sum_eq_one d n x
  unfold simplexField at hfield
  simpa [hnatural] using hfield

/-- If a scalar function differs from an affine barycentric model by at most
`eps` at every simplex lattice point, then its positive Bernstein sampling
recovery differs from the function value at `x` by at most `eps`, provided the
affine model is exact at `x`. -/
theorem simplexSamplingRecovery_error_le_of_affine_remainder
    (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint d → ℝ)
    (a : Fin (d + 1) → ℝ)
    (x : BarycentricPoint d) (eps : ℝ)
    (heps : 0 ≤ eps)
    (hmodelAtX : simplexAffineBarycentricValue d a x = w x)
    (hremainder : ∀ α : MultiIndex d n,
      |w (simplexLatticePoint d n hn α) -
        simplexAffineBarycentricValue d a
          (simplexLatticePoint d n hn α)| ≤ eps) :
    |simplexSamplingRecovery d n hn w x - w x| ≤ eps := by
  unfold simplexSamplingRecovery simplexSamplingCoefficients
  apply abs_weighted_sum_sub_target_le
    (weight := fun α : MultiIndex d n => simplexBasis d n α x)
    (approx := fun α => w (simplexLatticePoint d n hn α))
    (affine := fun α => simplexAffineBarycentricValue d a
      (simplexLatticePoint d n hn α))
    (target := w x) (eps := eps)
  · intro α
    exact simplexBasis_nonneg d n α x
  · exact simplexBasis_sum_eq_one d n x
  · have hrepro := simplexSamplingRecovery_affine_reproduction
      d n hn a x
    unfold simplexSamplingRecovery simplexSamplingCoefficients at hrepro
    simpa [mul_comm, hmodelAtX] using hrepro
  · exact heps
  · exact hremainder

end

end BernsteinObstacle
