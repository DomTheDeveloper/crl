import BernsteinObstacle.FiniteObstacle
import BernsteinObstacle.GlobalMesh
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Assembled Bernstein obstacle problem

This file joins the globally shared Bernstein coefficient representation to the
finite-dimensional variational-inequality and energy theory.  The feasible set
requires both nonnegative global gap coefficients and homogeneous boundary
coefficients.  Consequently a solution is pointwise nonpenetrating on every
element, satisfies the boundary constraint, minimizes the quadratic energy, and
obeys the verified recovery-to-solution energy estimates.
-/

/-- Minimal algebraic assembly data for a conforming Bernstein--Bézier mesh. -/
structure BernsteinAssembly (Element Dof : Type*) (d n : ℕ) where
  localDof : Element → MultiIndex d n → Dof
  boundaryDof : Set Dof

section Assembly

variable {Element Dof : Type*} [Fintype Dof] {d n : ℕ}

/-- Global coefficient vectors satisfying the obstacle and homogeneous boundary
constraints of an assembly. -/
def assemblyFeasibleSet (A : BernsteinAssembly Element Dof d n) :
    Set (Dof → ℝ) :=
  {c | globallyFeasible c ∧ ∀ i ∈ A.boundaryDof, c i = 0}

@[simp]
theorem mem_assemblyFeasibleSet_iff
    (A : BernsteinAssembly Element Dof d n) (c : Dof → ℝ) :
    c ∈ assemblyFeasibleSet A ↔
      globallyFeasible c ∧ ∀ i ∈ A.boundaryDof, c i = 0 := by
  rfl

/-- Clipping a coefficient vector that already satisfies the homogeneous
boundary values produces an assembled feasible vector. -/
theorem clipCoefficients_mem_assemblyFeasibleSet
    (A : BernsteinAssembly Element Dof d n) (c : Dof → ℝ)
    (hboundary : ∀ i ∈ A.boundaryDof, c i = 0) :
    clipCoefficients c ∈ assemblyFeasibleSet A := by
  constructor
  · exact clipCoefficients_mem c
  · exact boundary_zero_after_clipping A.boundaryDof c hboundary

/-- Every assembled feasible vector is pointwise nonnegative on every element. -/
theorem assemblyField_nonneg_of_feasible
    (A : BernsteinAssembly Element Dof d n) (c : Dof → ℝ)
    (hc : c ∈ assemblyFeasibleSet A)
    (T : Element) (x : BarycentricPoint d) :
    0 ≤ globalSimplexField A.localDof c T x := by
  exact globalSimplexField_nonneg A.localDof c hc.1 T x

/-- Every assembled feasible gap gives pointwise nonpenetration on every
physical element. -/
theorem assembly_noPenetration_of_feasible
    (A : BernsteinAssembly Element Dof d n)
    (ψ : Element → BarycentricPoint d → ℝ)
    (c : Dof → ℝ) (hc : c ∈ assemblyFeasibleSet A)
    (T : Element) (x : BarycentricPoint d) :
    ψ T x ≤ ψ T x + globalSimplexField A.localDof c T x := by
  have hgap : 0 ≤ globalSimplexField A.localDof c T x :=
    assemblyField_nonneg_of_feasible A c hc T x
  linarith

/-- The assembled obstacle variational inequality. -/
def IsAssembledObstacleSolution
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u : Dof → ℝ) : Prop :=
  IsDiscreteVISolution a f (assemblyFeasibleSet A) u

/-- An assembled VI solution satisfies the complete global coefficient
constraints. -/
theorem assembledSolution_mem_feasibleSet
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u : Dof → ℝ)
    (hu : IsAssembledObstacleSolution A a f u) :
    u ∈ assemblyFeasibleSet A :=
  hu.1

/-- An assembled VI solution is pointwise nonpenetrating throughout every
simplex, not merely at interpolation nodes. -/
theorem assembledSolution_noPenetration
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u : Dof → ℝ)
    (ψ : Element → BarycentricPoint d → ℝ)
    (hu : IsAssembledObstacleSolution A a f u)
    (T : Element) (x : BarycentricPoint d) :
    ψ T x ≤ ψ T x + globalSimplexField A.localDof u T x := by
  exact assembly_noPenetration_of_feasible A ψ u hu.1 T x

/-- An assembled VI solution satisfies the designated homogeneous boundary
coefficients. -/
theorem assembledSolution_boundary_zero
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u : Dof → ℝ)
    (hu : IsAssembledObstacleSolution A a f u) :
    ∀ i ∈ A.boundaryDof, u i = 0 :=
  hu.1.2

/-- Symmetry and positive semidefiniteness make every assembled VI solution an
energy minimizer over the assembled feasible set. -/
theorem assembledSolution_is_energyMinimizer
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u : Dof → ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hpsd : ∀ w : Dof → ℝ, 0 ≤ matrixBilin a w w)
    (hu : IsAssembledObstacleSolution A a f u) :
    IsDiscreteEnergyMinimizer a f (assemblyFeasibleSet A) u := by
  exact vi_solution_is_energy_minimizer
    a f (assemblyFeasibleSet A) u hsymm hpsd hu

/-- Any assembled feasible recovery vector controls the solution's quadratic
error energy. -/
theorem assembledSolution_half_error_le_energyGap
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u v : Dof → ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hu : IsAssembledObstacleSolution A a f u)
    (hv : v ∈ assemblyFeasibleSet A) :
    (1 / 2 : ℝ) * matrixBilin a (v - u) (v - u) ≤
      discreteEnergy a f v - discreteEnergy a f u := by
  exact vi_solution_half_error_le_energy_gap
    a f (assemblyFeasibleSet A) u v hsymm hu hv

/-- Coordinate coercivity turns an assembled feasible recovery vector into a
squared coefficient-error bound. -/
theorem assembledSolution_coercive_error_le_energyGap
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u v : Dof → ℝ) (μ : ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hu : IsAssembledObstacleSolution A a f u)
    (hv : v ∈ assemblyFeasibleSet A)
    (hcoercive : μ * coefficientNormSq (v - u) ≤
      matrixBilin a (v - u) (v - u)) :
    (μ / 2) * coefficientNormSq (v - u) ≤
      discreteEnergy a f v - discreteEnergy a f u := by
  exact vi_solution_coercive_error_le_energy_gap
    a f (assemblyFeasibleSet A) u v μ hsymm hu hv hcoercive

/-- The canonical clipped recovery estimate for an assembled obstacle problem. -/
theorem assembledSolution_coercive_error_le_clippedRecoveryGap
    (A : BernsteinAssembly Element Dof d n)
    (a : Dof → Dof → ℝ) (f u c : Dof → ℝ) (μ : ℝ)
    (hsymm : ∀ i j, a i j = a j i)
    (hu : IsAssembledObstacleSolution A a f u)
    (hboundary : ∀ i ∈ A.boundaryDof, c i = 0)
    (hcoercive : μ * coefficientNormSq (clipCoefficients c - u) ≤
      matrixBilin a (clipCoefficients c - u) (clipCoefficients c - u)) :
    (μ / 2) * coefficientNormSq (clipCoefficients c - u) ≤
      discreteEnergy a f (clipCoefficients c) - discreteEnergy a f u := by
  exact assembledSolution_coercive_error_le_energyGap
    A a f u (clipCoefficients c) μ hsymm hu
    (clipCoefficients_mem_assemblyFeasibleSet A c hboundary) hcoercive

end Assembly

end

end BernsteinObstacle
