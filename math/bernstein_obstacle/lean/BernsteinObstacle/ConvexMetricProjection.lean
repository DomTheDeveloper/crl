import BernsteinObstacle.ConvexConstraint
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

namespace BernsteinObstacle

noncomputable section

/-!
# Metric projection onto a closed convex coefficient target

This file replaces the abstract coefficient repair map by a chosen nearest-point
projection supplied by the Hilbert projection theorem. The finite feasibility
statement uses only that the chosen projection lands in the target set. The
nonexpansive estimate needed for quantitative repair bounds remains a separate
formal target.
-/

section ConvexMetricProjection

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A chosen nearest point in a nonempty closed convex set. -/
def convexMetricProjection
    (C : Set E) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) (x : E) : E :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex
      hCne hCclosed.isComplete hCconv x)

/-- The chosen metric projection belongs to the target set. -/
theorem convexMetricProjection_mem
    (C : Set E) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) (x : E) :
    convexMetricProjection C hCne hCclosed hCconv x ∈ C := by
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex
      hCne hCclosed.isComplete hCconv x)).1

/-- The chosen point realizes the distance infimum over the target set. -/
theorem convexMetricProjection_norm_eq_iInf
    (C : Set E) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) (x : E) :
    ‖x - convexMetricProjection C hCne hCclosed hCconv x‖ =
      ⨅ y : C, ‖x - y‖ := by
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex
      hCne hCclosed.isComplete hCconv x)).2

/-- Variational characterization of the chosen projection. -/
theorem convexMetricProjection_inner_le_zero
    (C : Set E) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) (x y : E) (hy : y ∈ C) :
    inner ℝ
      (x - convexMetricProjection C hCne hCclosed hCconv x)
      (y - convexMetricProjection C hCne hCclosed hCconv x) ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero hCconv
    (convexMetricProjection_mem C hCne hCclosed hCconv x)).1
  exact convexMetricProjection_norm_eq_iInf C hCne hCclosed hCconv x
  exact y
  exact hy

/-- Projecting every complete Bernstein coefficient onto a nonempty closed
convex target gives an exactly pointwise feasible vector field. -/
theorem metricProjected_simplexVectorFieldNat_pointwise_feasible
    (C : Set E) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (d n : ℕ) (c : (Fin (d + 1) → ℕ) → E) :
    simplexVectorFieldNat d n
        (fun α => convexMetricProjection C hCne hCclosed hCconv (c α)) ∈
      pointwiseConvexConstraint C d := by
  apply repaired_simplexVectorFieldNat_pointwise_feasible C hCconv
  intro y
  exact convexMetricProjection_mem C hCne hCclosed hCconv y

end ConvexMetricProjection

end

end BernsteinObstacle
