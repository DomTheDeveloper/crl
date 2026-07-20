import BernsteinObstacle.HilbertVI
import Mathlib.Tactic

open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Nested feasible-set Hilbert VI estimate

This file closes the coordinate-free minimizer-transfer step used by the moving
Bernstein cone argument. If a discrete feasible set is contained in the limit
feasible set, the continuous and discrete variational inequalities combine with
any discrete recovery point to control the full solution error by the recovery
distance gap.

The remaining concrete finite-element work is therefore isolated to constructing
a feasible Sobolev recovery sequence and proving its approximation rate.
-/

section NestedHilbertVI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nested discrete obstacle solution is controlled directly by any feasible
recovery point. This is the exact Hilbert-space endgame behind Mosco recovery. -/
theorem nested_hilbert_vi_recovery_error_sq
    (Kdisc K : Set E) (z udisc u r : E)
    (hsubset : Kdisc ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (hudisc : IsHilbertVISolution Kdisc z udisc)
    (hr : r ∈ Kdisc) :
    ‖udisc - u‖ ^ 2 ≤ ‖r - z‖ ^ 2 - ‖u - z‖ ^ 2 := by
  have hcontinuous :=
    hilbert_vi_pythagorean u udisc z (hu.2 udisc (hsubset hudisc.1))
  have hdiscrete :=
    hilbert_vi_pythagorean udisc r z (hudisc.2 r hr)
  nlinarith [sq_nonneg ‖r - udisc‖]

/-- The discrete distance to the unconstrained point is no larger than that of
any feasible recovery point. -/
theorem nested_hilbert_vi_distance_sq_le_recovery
    (Kdisc : Set E) (z udisc r : E)
    (hudisc : IsHilbertVISolution Kdisc z udisc)
    (hr : r ∈ Kdisc) :
    ‖udisc - z‖ ^ 2 ≤ ‖r - z‖ ^ 2 := by
  have h := hilbert_vi_pythagorean udisc r z (hudisc.2 r hr)
  nlinarith [sq_nonneg ‖r - udisc‖]

end NestedHilbertVI

end

end BernsteinObstacle
