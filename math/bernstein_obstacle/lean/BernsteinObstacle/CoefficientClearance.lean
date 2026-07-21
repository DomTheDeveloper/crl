import BernsteinObstacle.CoefficientCone
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Strict coefficient clearance certificates

A smooth recovery used in the obstacle argument is first given a strict
coefficient margin.  If every recovered coefficient stays closer than that
margin to the target coefficient, exact Bernstein feasibility follows.  These
lemmas provide the concrete finite-dimensional discharge of the clearance
premise used by `ClearanceSobolevFEMRecoveryData`.
-/

section CoefficientClearance

variable {ι : Type*}

/-- A coefficient vector with lower margin `delta` remains in the nonnegative
orthant under any coordinatewise perturbation of absolute size less than
`delta`. -/
theorem mem_coefficientCone_of_margin_of_abs_sub_lt
    (target candidate : ι → ℝ) (delta : ℝ)
    (hmargin : ∀ i, delta ≤ target i)
    (hclose : ∀ i, |candidate i - target i| < delta) :
    candidate ∈ coefficientCone ι := by
  intro i
  have hlower : -delta < candidate i - target i :=
    (abs_lt.mp (hclose i)).1
  linarith [hmargin i]

/-- A strict lower and upper coefficient margin survives every coordinatewise
perturbation smaller than that margin.  This is the bilateral box analogue of
the nonnegative-cone clearance lemma. -/
theorem coefficient_mem_Icc_of_margin_of_abs_sub_lt
    (lower upper target candidate : ι → ℝ) (delta : ℝ)
    (hlower : ∀ i, lower i + delta ≤ target i)
    (hupper : ∀ i, target i + delta ≤ upper i)
    (hclose : ∀ i, |candidate i - target i| < delta) :
    ∀ i, candidate i ∈ Set.Icc (lower i) (upper i) := by
  intro i
  have hneg : -delta < candidate i - target i :=
    (abs_lt.mp (hclose i)).1
  have hpos : candidate i - target i < delta :=
    (abs_lt.mp (hclose i)).2
  constructor <;> linarith [hlower i, hupper i]

/-- Constant lower and upper coefficient barriers are preserved by a strict
interior margin and a smaller coordinatewise perturbation. -/
theorem coefficient_mem_Icc_const_of_margin_of_abs_sub_lt
    (lower upper : ℝ) (target candidate : ι → ℝ) (delta : ℝ)
    (hlower : ∀ i, lower + delta ≤ target i)
    (hupper : ∀ i, target i + delta ≤ upper)
    (hclose : ∀ i, |candidate i - target i| < delta) :
    ∀ i, candidate i ∈ Set.Icc lower upper := by
  exact coefficient_mem_Icc_of_margin_of_abs_sub_lt
    (fun _ => lower) (fun _ => upper) target candidate delta
    hlower hupper hclose

end CoefficientClearance

end BernsteinObstacle
