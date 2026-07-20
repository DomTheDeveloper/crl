import BernsteinObstacle.AssembledObstacle
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Convex geometry of the assembled feasible set

The globally assembled obstacle constraints are the intersection of the
nonnegative coefficient orthant with homogeneous linear boundary equations.
This file proves nonemptiness and convexity and identifies coefficient clipping
as a nearest assembled feasible vector whenever the input already has the
required zero boundary values.
-/

section AssemblyConvex

variable {Element Dof : Type*} [Fintype Dof] {d n : ℕ}

/-- The assembled feasible set contains the zero coefficient vector. -/
theorem zero_mem_assemblyFeasibleSet
    (A : BernsteinAssembly Element Dof d n) :
    (0 : Dof → ℝ) ∈ assemblyFeasibleSet A := by
  constructor
  · intro i
    simp
  · intro i hi
    rfl

/-- The assembled feasible coefficient set is convex. -/
theorem assemblyFeasibleSet_convex
    (A : BernsteinAssembly Element Dof d n) :
    Convex ℝ (assemblyFeasibleSet A) := by
  intro c hc e he a b ha hb hab
  constructor
  · exact coefficientCone_convex Dof hc.1 he.1 ha hb hab
  · intro i hi
    change a * c i + b * e i = 0
    rw [hc.2 i hi, he.2 i hi]
    ring

/-- For boundary-compatible input data, clipping is no farther than any
assembled feasible competitor in coefficient Euclidean distance. -/
theorem clipCoefficients_sqDist_minimal_assembly
    (A : BernsteinAssembly Element Dof d n)
    (c v : Dof → ℝ)
    (hboundary : ∀ i ∈ A.boundaryDof, c i = 0)
    (hv : v ∈ assemblyFeasibleSet A) :
    coefficientSqDist c (clipCoefficients c) ≤ coefficientSqDist c v := by
  have hclip : clipCoefficients c ∈ assemblyFeasibleSet A :=
    clipCoefficients_mem_assemblyFeasibleSet A c hboundary
  exact clipCoefficients_sqDist_minimal c v hv.1

/-- The assembled projection inequality includes the distance remaining from the
clipped vector to every feasible competitor. -/
theorem clipCoefficients_projection_inequality_assembly
    (A : BernsteinAssembly Element Dof d n)
    (c v : Dof → ℝ)
    (hv : v ∈ assemblyFeasibleSet A) :
    coefficientSqDist c (clipCoefficients c) +
        coefficientSqDist (clipCoefficients c) v ≤
      coefficientSqDist c v := by
  exact clipCoefficients_projection_inequality c v hv.1

end AssemblyConvex

end

end BernsteinObstacle
