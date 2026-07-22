import BernsteinObstacle.GlobalSmoothSaturation
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Transporting coefficient-cone saturation to a physical norm

A fixed-degree finite-element polynomial can be represented either by its
Bernstein coefficient vector or as an element of a physical normed polynomial
space (for example, the local polynomial subspace equipped with the physical
`H¹` norm). These representations are related by a continuous linear
equivalence. This file proves the exact best-approximation comparison induced by
that equivalence.

The inverse operator norm controls the physical lower bound; the forward
operator norm controls the physical upper bound. Thus a coefficient-space
`Theta(h^2)` saturation theorem immediately becomes a physical-norm
`Theta(h^2)` theorem whenever the basis equivalence constants are uniformly
bounded on the fixed reference element.
-/

section Transport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The image of a feasible coefficient set in the physical representation. -/
def transportedFeasibleSet (Φ : E ≃L[ℝ] F) (K : Set E) : Set F :=
  Φ '' K

/-- A continuous linear equivalence gives a lower bound for the transported
best error through a bound on the inverse operator norm. -/
theorem bestApproximationError_transport_lower
    (Φ : E ≃L[ℝ] F) (u : E) (K : Set E) (Ainv : ℝ)
    (hK : K.Nonempty) (hAinv : 0 < Ainv)
    (hΦinv : ‖Φ.symm‖ ≤ Ainv) :
    bestApproximationError u K / Ainv ≤
      bestApproximationError (Φ u) (transportedFeasibleSet Φ K) := by
  have hImage : (transportedFeasibleSet Φ K).Nonempty := by
    rcases hK with ⟨v, hv⟩
    exact ⟨Φ v, ⟨v, hv, rfl⟩⟩
  unfold bestApproximationError transportedFeasibleSet
  apply (Metric.le_infDist hImage).2
  intro z hz
  rcases hz with ⟨v, hv, rfl⟩
  apply (div_le_iff₀ hAinv).2
  calc
    Metric.infDist u K ≤ dist u v := Metric.infDist_le_dist_of_mem hv
    _ = ‖u - v‖ := by rw [dist_eq_norm]
    _ = ‖Φ.symm (Φ u - Φ v)‖ := by simp
    _ ≤ ‖Φ.symm‖ * ‖Φ u - Φ v‖ :=
      Φ.symm.toContinuousLinearMap.le_opNorm (Φ u - Φ v)
    _ ≤ Ainv * ‖Φ u - Φ v‖ :=
      mul_le_mul_of_nonneg_right hΦinv (norm_nonneg _)
    _ = dist (Φ u) (Φ v) * Ainv := by
      rw [dist_eq_norm]
      ring

/-- If the coefficient feasible set is compact, the forward operator norm gives
an upper bound for the transported best error. -/
theorem bestApproximationError_transport_upper
    (Φ : E ≃L[ℝ] F) (u : E) (K : Set E) (Amap : ℝ)
    (hKcompact : IsCompact K) (hK : K.Nonempty)
    (hAmap : 0 ≤ Amap) (hΦ : ‖Φ‖ ≤ Amap) :
    bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ≤
      Amap * bestApproximationError u K := by
  obtain ⟨v, hv, hmin⟩ := hKcompact.exists_infDist_eq_dist hK u
  unfold bestApproximationError transportedFeasibleSet
  calc
    Metric.infDist (Φ u) (Φ '' K) ≤ dist (Φ u) (Φ v) :=
      Metric.infDist_le_dist_of_mem ⟨v, hv, rfl⟩
    _ = ‖Φ (u - v)‖ := by
      rw [dist_eq_norm, map_sub]
    _ ≤ ‖Φ‖ * ‖u - v‖ := Φ.toContinuousLinearMap.le_opNorm (u - v)
    _ ≤ Amap * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right hΦ (norm_nonneg _)
    _ = Amap * dist u v := by rw [dist_eq_norm]
    _ = Amap * Metric.infDist u K := by rw [hmin]

/-- Two-sided comparison of genuine best-approximation errors under a continuous
linear equivalence. -/
theorem bestApproximationError_transport_sandwich
    (Φ : E ≃L[ℝ] F) (u : E) (K : Set E) (Amap Ainv : ℝ)
    (hKcompact : IsCompact K) (hK : K.Nonempty)
    (hAmap : 0 ≤ Amap) (hAinv : 0 < Ainv)
    (hΦ : ‖Φ‖ ≤ Amap) (hΦinv : ‖Φ.symm‖ ≤ Ainv) :
    bestApproximationError u K / Ainv ≤
        bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ∧
      bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ≤
        Amap * bestApproximationError u K := by
  constructor
  · exact bestApproximationError_transport_lower
      Φ u K Ainv hK hAinv hΦinv
  · exact bestApproximationError_transport_upper
      Φ u K Amap hKcompact hK hAmap hΦ

/-- Terminal physical second-order saturation theorem.

A coefficient defect and feasible coefficient recovery give a coefficient-space
second-order sandwich. A uniformly bounded basis equivalence then transports it
to the physical normed polynomial space. -/
theorem physical_secondOrder_saturation_of_basisEquiv
    (Φ : E ≃L[ℝ] F)
    (u v : E) (K : Set E) (L : E →L[ℝ] ℝ)
    (gamma Acoeff Crec h Amap Ainv : ℝ)
    (hKcompact : IsCompact K) (hK : K.Nonempty) (hv : v ∈ K)
    (hAcoeff : 0 < Acoeff) (hh : 0 ≤ h)
    (hAmap : 0 ≤ Amap) (hAinv : 0 < Ainv)
    (hL : ‖L‖ ≤ Acoeff)
    (hdefect : ∀ w ∈ K, gamma * h ^ 2 ≤ |L (u - w)|)
    (hrecovery : ‖u - v‖ ≤ Crec * h ^ 2)
    (hΦ : ‖Φ‖ ≤ Amap) (hΦinv : ‖Φ.symm‖ ≤ Ainv) :
    (gamma / (Acoeff * Ainv)) * h ^ 2 ≤
        bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ∧
      bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ≤
        (Amap * Crec) * h ^ 2 := by
  have hcoeff := bestApproximationError_secondOrder_sandwich
    u v K L gamma Acoeff Crec h hK hv hAcoeff hL hdefect hrecovery
  have htransport := bestApproximationError_transport_sandwich
    Φ u K Amap Ainv hKcompact hK hAmap hAinv hΦ hΦinv
  constructor
  · calc
      (gamma / (Acoeff * Ainv)) * h ^ 2 =
          ((gamma / Acoeff) * h ^ 2) / Ainv := by ring
      _ ≤ bestApproximationError u K / Ainv := by
        exact div_le_div_of_nonneg_right hcoeff.1 hAinv.le
      _ ≤ bestApproximationError (Φ u) (transportedFeasibleSet Φ K) :=
        htransport.1
  · calc
      bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ≤
          Amap * bestApproximationError u K := htransport.2
      _ ≤ Amap * (Crec * h ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeff.2 hAmap
      _ = (Amap * Crec) * h ^ 2 := by ring

end Transport

end

end BernsteinObstacle
