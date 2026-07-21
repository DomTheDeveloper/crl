import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Operator-valued variational inequalities on inner cones

This file formalizes the algebraic core of the V6 Bernstein grand theorem.
Unlike the metric-projection layer, the operator need not be symmetric, linear,
or the gradient of an energy.
-/

section OperatorVI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A feasible point solves the operator variational inequality when its
operator residual has nonnegative pairing with every feasible direction. -/
def IsOperatorVISolution
    (K : Set E) (A : E → E) (f u : E) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪A u - f, v - u⟫_ℝ

/-- The continuous residual is nonnegative at every feasible competitor. -/
theorem operator_vi_residual_nonneg
    (K : Set E) (A : E → E) (f u v : E)
    (hu : IsOperatorVISolution K A f u)
    (hv : v ∈ K) :
    0 ≤ ⟪A u - f, v - u⟫_ℝ :=
  hu.2 v hv

/-- Reversing a feasible discrete direction changes the VI sign. -/
theorem operator_vi_reverse_direction_nonpos
    (K : Set E) (A : E → E) (f u v : E)
    (hu : IsOperatorVISolution K A f u)
    (hv : v ∈ K) :
    ⟪A u - f, u - v⟫_ℝ ≤ 0 := by
  have h := hu.2 v hv
  have hneg : u - v = -(v - u) := by abel
  rw [hneg, inner_neg_right]
  linarith

/-- Exact inner-cone Falk estimate. Strong monotonicity and Lipschitz control
are supplied in the precise pairings needed by the proof, allowing this lemma
to be reused for linear, nonlinear, symmetric, and nonsymmetric operators. -/
theorem operator_vi_innerCone_falk
    (K Kh : Set E) (A : E → E) (f u uh vh : E)
    (alpha L : ℝ)
    (hsub : Kh ⊆ K)
    (hu : IsOperatorVISolution K A f u)
    (huh : IsOperatorVISolution Kh A f uh)
    (hvh : vh ∈ Kh)
    (hmono :
      alpha * ‖uh - u‖ ^ 2 ≤ ⟪A uh - A u, uh - u⟫_ℝ)
    (hlipPair :
      ⟪A uh - A u, vh - u⟫_ℝ
        ≤ L * ‖uh - u‖ * ‖vh - u‖) :
    alpha * ‖uh - u‖ ^ 2
      ≤ L * ‖uh - u‖ * ‖vh - u‖
        + ⟪A u - f, vh - u⟫_ℝ := by
  have hcont : 0 ≤ ⟪A u - f, uh - u⟫_ℝ :=
    hu.2 uh (hsub huh.1)
  have hdisc : ⟪A uh - f, uh - vh⟫_ℝ ≤ 0 :=
    operator_vi_reverse_direction_nonpos Kh A f uh vh huh hvh
  have he : uh - u = (uh - vh) + (vh - u) := by abel
  have hA : A uh - A u = (A uh - f) - (A u - f) := by abel
  have hsum : A uh - f = (A uh - A u) + (A u - f) := by abel
  have hdiff :
      ⟪A uh - A u, uh - u⟫_ℝ =
        ⟪A uh - f, uh - u⟫_ℝ - ⟪A u - f, uh - u⟫_ℝ := by
    rw [hA, inner_sub_left]
  have hsplit :
      ⟪A uh - f, uh - u⟫_ℝ =
        ⟪A uh - f, uh - vh⟫_ℝ + ⟪A uh - f, vh - u⟫_ℝ := by
    rw [he, inner_add_right]
  have hresplit :
      ⟪A uh - f, vh - u⟫_ℝ =
        ⟪A uh - A u, vh - u⟫_ℝ + ⟪A u - f, vh - u⟫_ℝ := by
    rw [hsum, inner_add_left]
  calc
    alpha * ‖uh - u‖ ^ 2
        ≤ ⟪A uh - A u, uh - u⟫_ℝ := hmono
    _ = ⟪A uh - f, uh - u⟫_ℝ - ⟪A u - f, uh - u⟫_ℝ := hdiff
    _ ≤ ⟪A uh - f, uh - u⟫_ℝ := by linarith
    _ = ⟪A uh - f, uh - vh⟫_ℝ + ⟪A uh - f, vh - u⟫_ℝ := hsplit
    _ ≤ ⟪A uh - f, vh - u⟫_ℝ := by linarith
    _ = ⟪A uh - A u, vh - u⟫_ℝ + ⟪A u - f, vh - u⟫_ℝ := hresplit
    _ ≤ L * ‖uh - u‖ * ‖vh - u‖ + ⟪A u - f, vh - u⟫_ℝ := by
      linarith

/-- Denominator-free squared-error form of Young's inequality applied to the
Falk estimate. This is the stable form used by subsequent rate composition. -/
theorem operator_vi_error_sq_scaled
    (alpha L err app residual : ℝ)
    (halpha : 0 ≤ alpha)
    (hfalk : alpha * err ^ 2 ≤ L * err * app + residual) :
    alpha ^ 2 * err ^ 2
      ≤ L ^ 2 * app ^ 2 + 2 * alpha * residual := by
  nlinarith [sq_nonneg (alpha * err - L * app)]

/-- Quantitative rate composition in denominator-free form. -/
theorem operator_vi_rate_compose_scaled
    (alpha L err app residual rho Capp Cres : ℝ)
    (halpha : 0 ≤ alpha)
    (happ : app ^ 2 ≤ Capp ^ 2 * rho ^ 2)
    (hres : residual ≤ Cres * rho ^ 2)
    (hCapp : 0 ≤ Capp)
    (hCres : 0 ≤ Cres)
    (hL : 0 ≤ L)
    (hfalk : alpha * err ^ 2 ≤ L * err * app + residual) :
    alpha ^ 2 * err ^ 2
      ≤ (L ^ 2 * Capp ^ 2 + 2 * alpha * Cres) * rho ^ 2 := by
  have hbase :=
    operator_vi_error_sq_scaled alpha L err app residual halpha hfalk
  have happScaled :
      L ^ 2 * app ^ 2 ≤ L ^ 2 * (Capp ^ 2 * rho ^ 2) :=
    mul_le_mul_of_nonneg_left happ (sq_nonneg L)
  have htwoAlpha : 0 ≤ 2 * alpha := by linarith
  have hresScaled :
      (2 * alpha) * residual ≤ (2 * alpha) * (Cres * rho ^ 2) :=
    mul_le_mul_of_nonneg_left hres htwoAlpha
  nlinarith

/-- Same-cone perturbation estimate in squared, denominator-free form. -/
theorem operator_vi_sameCone_perturbation_scaled
    (alpha err defect : ℝ)
    (halpha : 0 ≤ alpha)
    (herr : 0 ≤ err)
    (hdefect : 0 ≤ defect)
    (hmonoPert : alpha * err ^ 2 ≤ defect * err) :
    alpha ^ 2 * err ^ 2 ≤ defect ^ 2 := by
  nlinarith [sq_nonneg (alpha * err - defect)]

end OperatorVI

end

end BernsteinObstacle
