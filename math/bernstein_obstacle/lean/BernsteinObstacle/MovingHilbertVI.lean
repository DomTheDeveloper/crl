import BernsteinObstacle.NestedHilbertVI
import BernsteinObstacle.SobolevFEMRecovery
import Mathlib.Tactic

open Filter
open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Moving nested Hilbert obstacle cones

This file turns strong feasible recovery for nested moving cones into strong
convergence of the corresponding Hilbert-space variational-inequality
solutions. It complements the scheduled Sobolev/FEM recovery infrastructure
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
  have hconst :
      Tendsto (fun _ : ℕ => ‖u - z‖ ^ 2) atTop (nhds (‖u - z‖ ^ 2)) :=
    tendsto_const_nhds
  have hgap :
      Tendsto (fun k => ‖r k - z‖ ^ 2 - ‖u - z‖ ^ 2) atTop (nhds 0) := by
    simpa using hsquare.sub hconst
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
  unfold StronglyConverges at hr
  have hsub : Tendsto (fun k => r k - z) atTop (nhds (u - z)) :=
    hr.sub tendsto_const_nhds
  have hnorm : Tendsto (fun k => ‖r k - z‖) atTop (nhds ‖u - z‖) :=
    hsub.norm
  have hsquare :
      Tendsto (fun k => ‖r k - z‖ ^ 2) atTop (nhds (‖u - z‖ ^ 2)) :=
    hnorm.pow 2
  have hconst :
      Tendsto (fun _ : ℕ => ‖u - z‖ ^ 2) atTop (nhds (‖u - z‖ ^ 2)) :=
    tendsto_const_nhds
  let gap : ℕ → ℝ := fun k => ‖r k - z‖ ^ 2 - ‖u - z‖ ^ 2
  have hgap : Tendsto gap atTop (nhds 0) := by
    simpa [gap] using hsquare.sub hconst
  let err : ℕ → ℝ := fun k => Real.sqrt (gap k)
  have herr : Tendsto err atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hgap
    simpa only [err, Function.comp_apply, Real.sqrt_zero] using hsqrt
  exact stronglyConverges_of_recovery_closeness
    udisc (fun _ => u) u err tendsto_const_nhds
    (fun k => by
      apply Real.le_sqrt_of_sq_le
      exact nested_hilbert_vi_recovery_error_sq
        (Kdisc k) K z (udisc k) u (r k)
        (hsubset k) hu (hudisc k) (hrmem k))
    herr

/-- The threshold-form Sobolev/FEM recovery package is sufficient by itself to
prove strong convergence of nested projection-form obstacle VI solutions. No
separate solution-to-recovery error hypothesis is required. -/
theorem ThresholdSobolevFEMRecoveryData.hilbertVISolutions_strongConvergence
    (D : ThresholdSobolevFEMRecoveryData E)
    (z u : E) (udisc : ℕ → E)
    (hu : IsHilbertVISolution D.limitCone z u)
    (hudisc : ∀ n, IsHilbertVISolution (D.discreteCone n) z (udisc n)) :
    StronglyConverges udisc u := by
  obtain ⟨w, R, stage, err, hw, hstage, hmem, hclose, herr⟩ :=
    D.scheduledRecovery u hu.1
  have hrecovery : StronglyConverges (fun n => R (stage n) n) u :=
    diagonalRecovery_stronglyConverges
      w R stage u err hw hstage hclose herr
  exact nested_hilbert_vi_strongConvergence_of_recovery
    D.discreteCone D.limitCone z u udisc (fun n => R (stage n) n)
    D.inner hu hudisc hmem hrecovery

/-- The same threshold-form package simultaneously yields Mosco convergence and
direct strong convergence of the projection-form VI solutions. -/
theorem ThresholdSobolevFEMRecoveryData.mosco_and_hilbertVISolutions_strongConvergence
    (D : ThresholdSobolevFEMRecoveryData E)
    (z u : E) (udisc : ℕ → E)
    (hu : IsHilbertVISolution D.limitCone z u)
    (hudisc : ∀ n, IsHilbertVISolution (D.discreteCone n) z (udisc n)) :
    MoscoConverges D.discreteCone D.limitCone ∧ StronglyConverges udisc u := by
  exact ⟨D.moscoConverges,
    D.hilbertVISolutions_strongConvergence z u udisc hu hudisc⟩

end MovingHilbertVI

end

end BernsteinObstacle
