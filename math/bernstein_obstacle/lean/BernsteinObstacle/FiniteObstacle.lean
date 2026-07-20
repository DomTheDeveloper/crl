import BernsteinObstacle.Energy
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Finite-dimensional obstacle variational inequalities

This file packages the algebraic variational inequality solved by a conforming
finite-element discretization.  It proves that a feasible VI solution minimizes
the symmetric positive-semidefinite quadratic energy, and records the exact
energy/error estimate for every feasible competitor.
-/

section FiniteObstacle

variable {ι : Type*} [Fintype ι]

/-- A feasible vector satisfying the discrete obstacle variational inequality. -/
def IsDiscreteVISolution
    (a : ι → ι → ℝ) (f : ι → ℝ)
    (K : Set (ι → ℝ)) (u : ι → ℝ) : Prop :=
  u ∈ K ∧
    ∀ v ∈ K,
      vectorLoad f (v - u) ≤ matrixBilin a u (v - u)

/-- A global minimizer of the discrete energy over the feasible set. -/
def IsDiscreteEnergyMinimizer
    (a : ι → ι → ℝ) (f : ι → ℝ)
    (K : Set (ι → ℝ)) (u : ι → ℝ) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, discreteEnergy a f u ≤ discreteEnergy a f v

/-- A discrete VI solution minimizes the quadratic energy whenever the
stiffness matrix is symmetric and positive semidefinite. -/
theorem vi_solution_is_energy_minimizer
    (a : ι → ι → ℝ) (f : ι → ℝ)
    (K : Set (ι → ℝ)) (u : ι → ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hpsd : ∀ w : ι → ℝ, 0 ≤ matrixBilin a w w)
    (hu : IsDiscreteVISolution a f K u) :
    IsDiscreteEnergyMinimizer a f K u := by
  constructor
  · exact hu.1
  · intro v hv
    have hvi := hu.2 v hv
    have hid := discreteEnergy_difference_identity a f u v hsymm
    have hquad : 0 ≤ (1 / 2 : ℝ) * matrixBilin a (v - u) (v - u) := by
      positivity
    have hres : 0 ≤ matrixBilin a u (v - u) - vectorLoad f (v - u) := by
      linarith
    linarith

/-- Every feasible competitor controls the error energy of a discrete VI
solution.  This is the exact finite-dimensional recovery-to-minimizer bridge. -/
theorem vi_solution_half_error_le_energy_gap
    (a : ι → ι → ℝ) (f : ι → ℝ)
    (K : Set (ι → ℝ)) (u v : ι → ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hu : IsDiscreteVISolution a f K u)
    (hv : v ∈ K) :
    (1 / 2 : ℝ) * matrixBilin a (v - u) (v - u) ≤
      discreteEnergy a f v - discreteEnergy a f u := by
  exact half_error_energy_le a f u v hsymm (hu.2 v hv)

/-- Under a coordinate coercivity estimate, every feasible recovery competitor
bounds the squared coefficient error of the discrete VI solution. -/
theorem vi_solution_coercive_error_le_energy_gap
    (a : ι → ι → ℝ) (f : ι → ℝ)
    (K : Set (ι → ℝ)) (u v : ι → ℝ) (μ : ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hu : IsDiscreteVISolution a f K u)
    (hv : v ∈ K)
    (hcoercive : μ * coefficientNormSq (v - u) ≤
      matrixBilin a (v - u) (v - u)) :
    (μ / 2) * coefficientNormSq (v - u) ≤
      discreteEnergy a f v - discreteEnergy a f u := by
  exact coercive_error_le_energy a f u v μ hsymm (hu.2 v hv) hcoercive

/-- The feasible set of globally nonnegative coefficients gives the canonical
finite Bernstein obstacle VI. -/
def IsCoefficientObstacleSolution
    (a : ι → ι → ℝ) (f : ι → ℝ) (u : ι → ℝ) : Prop :=
  IsDiscreteVISolution a f (coefficientCone ι) u

end FiniteObstacle

end BernsteinObstacle
