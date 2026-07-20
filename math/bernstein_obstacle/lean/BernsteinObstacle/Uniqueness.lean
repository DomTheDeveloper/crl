import BernsteinObstacle.AssembledObstacle
import BernsteinObstacle.CoefficientNorm
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Uniqueness under positive coercivity

A symmetric stiffness form with a positive coordinate-coercivity constant has at
most one solution of the finite obstacle variational inequality.  The proof uses
the already-verified minimization and energy-gap estimates: two VI solutions
minimize the same energy, so their energy gap is zero, while coercivity forces
their coefficient squared distance to vanish.
-/

section Uniqueness

variable {ι : Type*} [Fintype ι]

/-- The coefficient squared norm vanishes exactly at the zero vector. -/
theorem coefficientNormSq_eq_zero_iff (w : ι → ℝ) :
    coefficientNormSq w = 0 ↔ w = 0 := by
  constructor
  · intro h
    funext i
    have hterm : (w i) ^ 2 = 0 := by
      have hnonneg : ∀ j, 0 ≤ (w j) ^ 2 := fun j => sq_nonneg (w j)
      exact Finset.sum_eq_zero_iff_of_nonneg hnonneg |>.mp h i (Finset.mem_univ i)
    nlinarith
  · intro h
    rw [h]
    simp [coefficientNormSq]

/-- A symmetric positively coercive finite obstacle VI has at most one solution. -/
theorem discreteVISolution_unique_of_coercive
    (a : ι → ι → ℝ) (f : ι → ℝ)
    (K : Set (ι → ℝ)) (u v : ι → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hsymm : ∀ i j, a i j = a j i)
    (hcoercive : ∀ w : ι → ℝ,
      μ * coefficientNormSq w ≤ matrixBilin a w w)
    (hu : IsDiscreteVISolution a f K u)
    (hv : IsDiscreteVISolution a f K v) :
    u = v := by
  have hnorm_nonneg : ∀ w : ι → ℝ, 0 ≤ coefficientNormSq w := by
    intro w
    unfold coefficientNormSq
    positivity
  have hpsd : ∀ w : ι → ℝ, 0 ≤ matrixBilin a w w := by
    intro w
    exact le_trans (mul_nonneg (le_of_lt hμ) (hnorm_nonneg w)) (hcoercive w)
  have huMin := vi_solution_is_energy_minimizer a f K u hsymm hpsd hu
  have hvMin := vi_solution_is_energy_minimizer a f K v hsymm hpsd hv
  have hEnergyEq : discreteEnergy a f v - discreteEnergy a f u = 0 := by
    have huv := huMin.2 v hv.1
    have hvu := hvMin.2 u hu.1
    linarith
  have herr := vi_solution_coercive_error_le_energy_gap
    a f K u v μ hsymm hu hv.1 (hcoercive (v - u))
  have hnorm : coefficientNormSq (v - u) = 0 := by
    have hhalf : 0 < μ / 2 := by positivity
    have hle : (μ / 2) * coefficientNormSq (v - u) ≤ 0 := by
      simpa [hEnergyEq] using herr
    have hnonneg := hnorm_nonneg (v - u)
    nlinarith
  have hzero : v - u = 0 := (coefficientNormSq_eq_zero_iff (v - u)).1 hnorm
  exact (sub_eq_zero.mp hzero).symm

end Uniqueness

section AssembledUniqueness

variable {Element Dof : Type*} [Fintype Dof] {d n : ℕ}

/-- The assembled Bernstein obstacle VI has at most one solution under a
positive uniform coefficient-coercivity estimate. -/
theorem assembledObstacleSolution_unique_of_coercive
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u v : Dof → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hsymm : ∀ i j, a i j = a j i)
    (hcoercive : ∀ w : Dof → ℝ,
      μ * coefficientNormSq w ≤ matrixBilin a w w)
    (hu : IsAssembledObstacleSolution A a f u)
    (hv : IsAssembledObstacleSolution A a f v) :
    u = v := by
  exact discreteVISolution_unique_of_coercive
    a f (assemblyFeasibleSet A) u v μ hμ hsymm hcoercive hu hv

end AssembledUniqueness

end

end BernsteinObstacle
