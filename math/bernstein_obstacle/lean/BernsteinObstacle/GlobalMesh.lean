import BernsteinObstacle.CoefficientCone
import BernsteinObstacle.Simplex
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Global shared Bernstein coefficients

This file isolates the algebraic part of conformity used by a conforming
Bernstein--Bézier finite-element mesh.  A local control coefficient is obtained
from one globally shared degree of freedom through `localDof`.  Thus two local
coefficients on adjacent elements are identified exactly when they map to the
same global degree of freedom.  Coefficientwise clipping is performed globally,
so this identification, and hence the shared trace data, is preserved.
-/

section SharedCoefficients

variable {Element Dof : Type*} {d n : ℕ}

/-- Pull a globally shared coefficient vector back to the local Bernstein
coefficients of one element. -/
def localCoefficients
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (T : Element) : MultiIndex d n → ℝ :=
  fun α => c (localDof T α)

/-- The simplicial Bernstein field on an element induced by globally shared
control coefficients. -/
def globalSimplexField
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (T : Element) (x : BarycentricPoint d) : ℝ :=
  simplexField d n (localCoefficients localDof c T) x

/-- Global nonnegativity of all shared degrees of freedom. -/
def globallyFeasible (c : Dof → ℝ) : Prop :=
  c ∈ coefficientCone Dof

@[simp]
theorem globallyFeasible_iff (c : Dof → ℝ) :
    globallyFeasible c ↔ ∀ i, 0 ≤ c i := by
  rfl

/-- A globally feasible coefficient vector restricts to a feasible coefficient
vector on every element. -/
theorem localCoefficients_nonneg
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (hc : globallyFeasible c)
    (T : Element) (α : MultiIndex d n) :
    0 ≤ localCoefficients localDof c T α := by
  exact hc (localDof T α)

/-- Global coefficient feasibility certifies pointwise nonnegativity on every
element of the mesh. -/
theorem globalSimplexField_nonneg
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (hc : globallyFeasible c)
    (T : Element) (x : BarycentricPoint d) :
    0 ≤ globalSimplexField localDof c T x := by
  exact simplexField_nonneg d n (localCoefficients localDof c T)
    (fun α => localCoefficients_nonneg localDof c hc T α) x

/-- Pullback commutes exactly with global clipping. -/
theorem localCoefficients_clip
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (T : Element) :
    localCoefficients localDof (clipCoefficients c) T =
      clipSimplex d n (localCoefficients localDof c T) := by
  funext α
  rfl

/-- If two local Bernstein coefficients are the same global degree of freedom,
they remain equal after clipping.  This is the algebraic core of
conformity-preserving shared-face clipping. -/
theorem clipped_local_coeff_eq_of_shared
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ)
    {T U : Element} {α β : MultiIndex d n}
    (hshared : localDof T α = localDof U β) :
    localCoefficients localDof (clipCoefficients c) T α =
      localCoefficients localDof (clipCoefficients c) U β := by
  simp [localCoefficients, hshared]

/-- Global clipping produces a pointwise nonnegative field on every element. -/
theorem clipped_globalSimplexField_nonneg
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (T : Element) (x : BarycentricPoint d) :
    0 ≤ globalSimplexField localDof (clipCoefficients c) T x := by
  exact globalSimplexField_nonneg localDof (clipCoefficients c)
    (clipCoefficients_mem c) T x

/-- A globally shared obstacle plus a clipped Bernstein gap is nonpenetrating
at every point of every element. -/
theorem global_noPenetration_after_clipping
    (localDof : Element → MultiIndex d n → Dof)
    (ψ : Element → BarycentricPoint d → ℝ)
    (c : Dof → ℝ) (T : Element) (x : BarycentricPoint d) :
    ψ T x ≤ ψ T x + globalSimplexField localDof (clipCoefficients c) T x := by
  have hgap : 0 ≤ globalSimplexField localDof (clipCoefficients c) T x :=
    clipped_globalSimplexField_nonneg localDof c T x
  linarith

/-- Clipping preserves a homogeneous boundary coefficient. -/
theorem clipCoefficients_eq_zero_of_eq_zero
    (c : Dof → ℝ) {i : Dof} (hi : c i = 0) :
    clipCoefficients c i = 0 := by
  simp [clipCoefficients, clip, hi]

/-- If all designated boundary degrees of freedom are zero, they remain zero
after global clipping. -/
theorem boundary_zero_after_clipping
    (boundaryDof : Set Dof) (c : Dof → ℝ)
    (hc : ∀ i ∈ boundaryDof, c i = 0) :
    ∀ i ∈ boundaryDof, clipCoefficients c i = 0 := by
  intro i hi
  exact clipCoefficients_eq_zero_of_eq_zero c (hc i hi)

/-- Global clipping is monotone at every local coefficient. -/
theorem localCoefficient_le_clipped
    (localDof : Element → MultiIndex d n → Dof)
    (c : Dof → ℝ) (T : Element) (α : MultiIndex d n) :
    localCoefficients localDof c T α ≤
      localCoefficients localDof (clipCoefficients c) T α := by
  exact coefficient_le_clipCoefficients c (localDof T α)

end SharedCoefficients

end

end BernsteinObstacle
