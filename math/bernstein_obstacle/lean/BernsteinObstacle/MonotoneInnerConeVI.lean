import BernsteinObstacle.MonotoneInnerConeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Strongly monotone variational inequalities on certified inner cones

This file formalizes the operator-level inequality behind the nonlinear and
nonsymmetric Bernstein–Bézier extension. The operator is represented through
its Riesz vector in a real Hilbert space; no potential, symmetry, or linearity is
assumed.
-/

section MonotoneInnerConeVI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Variational-inequality solution for a vector-valued operator represented in
a real Hilbert space. -/
def IsOperatorVISolution (K : Set E) (F : E → E) (u : E) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪F u, v - u⟫_ℝ

/-- **Bernstein–Bézier Inner-Cone Falk Theorem: operator core.**
For nested certified feasible sets, strong monotonicity and a Lipschitz bound
reduce the solution error to a recovery distance and the continuous
complementarity residual. -/
theorem monotoneInnerCone_operator_core
    (Kdisc K : Set E) (F : E → E)
    (u udisc recovery : E) (α L : ℝ)
    (hsubset : Kdisc ⊆ K)
    (hu : IsOperatorVISolution K F u)
    (hudisc : IsOperatorVISolution Kdisc F udisc)
    (hrecovery : recovery ∈ Kdisc)
    (hmono :
      α * ‖udisc - u‖ ^ 2 ≤
        ⟪F udisc - F u, udisc - u⟫_ℝ)
    (hL : 0 ≤ L)
    (hlip : ‖F udisc - F u‖ ≤ L * ‖udisc - u‖) :
    α * ‖udisc - u‖ ^ 2 ≤
      L * ‖udisc - u‖ * ‖recovery - u‖ +
        ⟪F u, recovery - u⟫_ℝ := by
  have hcontinuous : 0 ≤ ⟪F u, udisc - u⟫_ℝ :=
    hu.2 udisc (hsubset hudisc.1)
  have hdiscrete : 0 ≤ ⟪F udisc, recovery - udisc⟫_ℝ :=
    hudisc.2 recovery hrecovery
  have hcompetitor :
      ⟪F udisc, udisc - u⟫_ℝ ≤
        ⟪F udisc, recovery - u⟫_ℝ := by
    have hdecomp : recovery - u = (recovery - udisc) + (udisc - u) := by
      abel
    rw [hdecomp, inner_add_right]
    linarith
  have hoperator :
      ⟪F udisc - F u, udisc - u⟫_ℝ ≤
        ⟪F udisc, recovery - u⟫_ℝ := by
    rw [inner_sub_left]
    linarith
  have hcauchy :
      ⟪F udisc - F u, recovery - u⟫_ℝ ≤
        ‖F udisc - F u‖ * ‖recovery - u‖ :=
    real_inner_le_norm (F udisc - F u) (recovery - u)
  have hlipRecovery :
      ‖F udisc - F u‖ * ‖recovery - u‖ ≤
        (L * ‖udisc - u‖) * ‖recovery - u‖ :=
    mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  have hsplit :
      ⟪F udisc, recovery - u⟫_ℝ =
        ⟪F udisc - F u, recovery - u⟫_ℝ +
          ⟪F u, recovery - u⟫_ℝ := by
    rw [inner_sub_left]
    ring
  calc
    α * ‖udisc - u‖ ^ 2 ≤
        ⟪F udisc - F u, udisc - u⟫_ℝ := hmono
    _ ≤ ⟪F udisc, recovery - u⟫_ℝ := hoperator
    _ = ⟪F udisc - F u, recovery - u⟫_ℝ +
          ⟪F u, recovery - u⟫_ℝ := hsplit
    _ ≤ (‖F udisc - F u‖ * ‖recovery - u‖) +
          ⟪F u, recovery - u⟫_ℝ :=
      add_le_add_right hcauchy _
    _ ≤ ((L * ‖udisc - u‖) * ‖recovery - u‖) +
          ⟪F u, recovery - u⟫_ℝ :=
      add_le_add_right hlipRecovery _
    _ = L * ‖udisc - u‖ * ‖recovery - u‖ +
          ⟪F u, recovery - u⟫_ℝ := by ring

/-- Squared-error form of the operator-level Inner-Cone Falk theorem. -/
theorem monotoneInnerCone_operator_falk_sq
    (Kdisc K : Set E) (F : E → E)
    (u udisc recovery : E) (α L : ℝ)
    (hsubset : Kdisc ⊆ K)
    (hu : IsOperatorVISolution K F u)
    (hudisc : IsOperatorVISolution Kdisc F udisc)
    (hrecovery : recovery ∈ Kdisc)
    (hα : 0 < α)
    (hL : 0 ≤ L)
    (hmono :
      α * ‖udisc - u‖ ^ 2 ≤
        ⟪F udisc - F u, udisc - u⟫_ℝ)
    (hlip : ‖F udisc - F u‖ ≤ L * ‖udisc - u‖) :
    ‖udisc - u‖ ^ 2 ≤
      (L ^ 2 / α ^ 2) * ‖recovery - u‖ ^ 2 +
        (2 / α) * ⟪F u, recovery - u⟫_ℝ := by
  apply monotoneInnerCone_falk_sq
    ‖udisc - u‖ ‖recovery - u‖
      ⟪F u, recovery - u⟫_ℝ α L hα
  exact monotoneInnerCone_operator_core
    Kdisc K F u udisc recovery α L
    hsubset hu hudisc hrecovery hmono hL hlip

end MonotoneInnerConeVI

end

end BernsteinObstacle
