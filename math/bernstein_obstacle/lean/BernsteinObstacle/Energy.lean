import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Finite-dimensional obstacle energy algebra

This file formalizes the exact quadratic-energy identity behind the transfer
from a feasible recovery approximation to the discrete obstacle minimizer.  It
is intentionally stated for an arbitrary finite symmetric stiffness matrix;
no coordinate choice or particular finite-element basis is assumed.
-/

section FiniteEnergy

variable {ι : Type*} [Fintype ι]

/-- Bilinear form represented by a finite matrix. -/
def matrixBilin (a : ι → ι → ℝ) (u v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * u i * v j

/-- Linear load represented by a finite vector. -/
def vectorLoad (f u : ι → ℝ) : ℝ :=
  ∑ i, f i * u i

/-- Symmetric quadratic obstacle energy. -/
def discreteEnergy (a : ι → ι → ℝ) (f u : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * matrixBilin a u u - vectorLoad f u

/-- Coordinate squared norm. -/
def coefficientNormSq (u : ι → ℝ) : ℝ :=
  ∑ i, (u i) ^ 2

@[simp]
theorem matrixBilin_add_left (a : ι → ι → ℝ) (u v w : ι → ℝ) :
    matrixBilin a (u + v) w = matrixBilin a u w + matrixBilin a v w := by
  simp [matrixBilin, add_mul, mul_add, Finset.sum_add_distrib]

@[simp]
theorem matrixBilin_add_right (a : ι → ι → ℝ) (u v w : ι → ℝ) :
    matrixBilin a u (v + w) = matrixBilin a u v + matrixBilin a u w := by
  simp [matrixBilin, mul_add, Finset.sum_add_distrib]

@[simp]
theorem matrixBilin_sub_left (a : ι → ι → ℝ) (u v w : ι → ℝ) :
    matrixBilin a (u - v) w = matrixBilin a u w - matrixBilin a v w := by
  simp [matrixBilin, sub_mul, mul_sub, Finset.sum_sub_distrib]

@[simp]
theorem matrixBilin_sub_right (a : ι → ι → ℝ) (u v w : ι → ℝ) :
    matrixBilin a u (v - w) = matrixBilin a u v - matrixBilin a u w := by
  simp [matrixBilin, mul_sub, Finset.sum_sub_distrib]

@[simp]
theorem vectorLoad_add (f u v : ι → ℝ) :
    vectorLoad f (u + v) = vectorLoad f u + vectorLoad f v := by
  simp [vectorLoad, mul_add, Finset.sum_add_distrib]

@[simp]
theorem vectorLoad_sub (f u v : ι → ℝ) :
    vectorLoad f (u - v) = vectorLoad f u - vectorLoad f v := by
  simp [vectorLoad, mul_sub, Finset.sum_sub_distrib]

/-- Matrix symmetry gives symmetry of the represented bilinear form. -/
theorem matrixBilin_symm (a : ι → ι → ℝ)
    (hsymm : ∀ i j, a i j = a j i) (u v : ι → ℝ) :
    matrixBilin a u v = matrixBilin a v u := by
  unfold matrixBilin
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsymm j i]
  ring

/-- Exact polarization identity for the quadratic energy. -/
theorem discreteEnergy_difference_identity
    (a : ι → ι → ℝ) (f u v : ι → ℝ)
    (hsymm : ∀ i j, a i j = a j i) :
    discreteEnergy a f v - discreteEnergy a f u =
      (1 / 2 : ℝ) * matrixBilin a (v - u) (v - u) +
        (matrixBilin a u (v - u) - vectorLoad f (v - u)) := by
  let w : ι → ℝ := v - u
  have hvw : v = u + w := by
    funext i
    simp [w]
  have hquadw :
      matrixBilin a v v =
        matrixBilin a u u + 2 * matrixBilin a u w +
          matrixBilin a w w := by
    rw [hvw, matrixBilin_add_left, matrixBilin_add_right,
      matrixBilin_add_right]
    have hcross : matrixBilin a w u = matrixBilin a u w :=
      matrixBilin_symm a hsymm w u
    linarith
  have hloadw :
      vectorLoad f v = vectorLoad f u + vectorLoad f w := by
    rw [hvw, vectorLoad_add]
  have hquad :
      matrixBilin a v v =
        matrixBilin a u u + 2 * matrixBilin a u (v - u) +
          matrixBilin a (v - u) (v - u) := by
    simpa [w] using hquadw
  have hload :
      vectorLoad f v = vectorLoad f u + vectorLoad f (v - u) := by
    simpa [w] using hloadw
  rw [discreteEnergy, discreteEnergy, hquad, hload]
  ring

/-- The variational inequality makes the residual term in the exact energy
identity nonnegative. -/
theorem half_error_energy_le
    (a : ι → ι → ℝ) (f u v : ι → ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hvi : vectorLoad f (v - u) ≤ matrixBilin a u (v - u)) :
    (1 / 2 : ℝ) * matrixBilin a (v - u) (v - u) ≤
      discreteEnergy a f v - discreteEnergy a f u := by
  rw [discreteEnergy_difference_identity a f u v hsymm]
  linarith

/-- Coercivity turns the exact energy inequality into a squared coefficient
error estimate. -/
theorem coercive_error_le_energy
    (a : ι → ι → ℝ) (f u v : ι → ℝ) (μ : ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hvi : vectorLoad f (v - u) ≤ matrixBilin a u (v - u))
    (hcoercive : μ * coefficientNormSq (v - u) ≤
      matrixBilin a (v - u) (v - u)) :
    (μ / 2) * coefficientNormSq (v - u) ≤
      discreteEnergy a f v - discreteEnergy a f u := by
  have hhalf := half_error_energy_le a f u v hsymm hvi
  nlinarith

end FiniteEnergy

end

end BernsteinObstacle
