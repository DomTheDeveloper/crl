import BernsteinObstacle.NestedHilbertVI
import BernsteinObstacle.Mosco
import Mathlib.Tactic

open Filter
open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Moving nested Hilbert obstacle cones

This file turns strong feasible recovery for nested moving cones into strong
convergence of the corresponding Hilbert-space variational-inequality
solutions.  It complements the scheduled Sobolev/FEM recovery infrastructure
with a direct coordinate-free projection proof.
-/

section MovingHilbertVI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong feasible recovery forces the squared error of nested VI solutions to
converge to zero. -/
theorem nested_hilbert_vi_error_sq_tendsto_zero_of_recovery
    (Kdisc : ℕ → Set E) (K : Set E)
    (z u : E) (udisc r : ℕ → E)
    (hsubset : ∀ k, Kdisc k ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (hudisc : ∀ k, IsHilbertVISolution (Kdisc k) z (udisc k))
    (hrmem : ∀ k, r k ∈ Kdisc k)
    (hr : StronglyConverges r u) :
    Tendsto (fun k => ‖udisc k - u‖ ^ 2) atTop (nhds 0) := by
  unfold StronglyConverges at hr
  have hsub : Tendsto (fun k => r k - z) atTop (nhds (u - z)) :=
    hr.sub tendsto_const_nhds
  have hnorm : Tendsto (fun k => ‖r k - z‖) atTop (nhds ‖u - z‖) :=
    hsub.norm
  have hsquare :
      Tendsto (fun k => ‖r k - z‖ ^ 2) atTop (nhds (‖u - z‖ ^ 2)) :=
    hnorm.pow 2
  have hgap :
      Tendsto (fun k => ‖r k - z‖ ^ 2 - ‖u - z‖ ^ 2) atTop (nhds 0) := by
    simpa using hsquare.sub tendsto_const_nhds
  exact squeeze_zero'
    (Eventually.of_forall (fun k => sq_nonneg ‖udisc k - u‖))
    (Eventually.of_forall (fun k =>
      nested_hilbert_vi_recovery_error_sq
        (Kdisc k) K z (udisc k) u (r k)
        (hsubset k) hu (hudisc k) (hrmem k)))
    hgap

/-- Strong feasible recovery implies strong convergence of the nested discrete
VI solutions. -/
theorem nested_hilbert_vi_strongConvergence_of_recovery
    (Kdisc : ℕ → Set E) (K : Set E)
    (z u : E) (udisc r : ℕ → E)
    (hsubset : ∀ k, Kdisc k ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (hudisc : ∀ k, IsHilbertVISolution (Kdisc k) z (udisc k))
    (hrmem : ∀ k, r k ∈ Kdisc k)
    (hr : StronglyConverges r u) :
    StronglyConverges udisc u := by
  have hsquare := nested_hilbert_vi_error_sq_tendsto_zero_of_recovery
    Kdisc K z u udisc r hsubset hu hudisc hrmem hr
  have hnorm : Tendsto (fun k => ‖udisc k - u‖) atTop (nhds 0) := by
    have hsqrt := Real.continuousAt_sqrt.tendsto.comp hsquare
    simpa using hsqrt
  unfold StronglyConverges
  exact tendsto_iff_norm_tendsto_zero.mpr hnorm

end MovingHilbertVI

end

end BernsteinObstacle
