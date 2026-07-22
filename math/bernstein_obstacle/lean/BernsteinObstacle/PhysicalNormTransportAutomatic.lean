import BernsteinObstacle.PhysicalNormTransport
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

section AutomaticConstants

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical forward basis constant. -/
def basisForwardConstant (Φ : E ≃L[ℝ] F) : ℝ :=
  ‖Φ.toContinuousLinearMap‖

/-- Canonical strictly positive inverse basis constant. -/
def basisInverseConstant (Φ : E ≃L[ℝ] F) : ℝ :=
  max ‖Φ.symm.toContinuousLinearMap‖ 1

/-- The forward basis constant is nonnegative. -/
theorem basisForwardConstant_nonneg (Φ : E ≃L[ℝ] F) :
    0 ≤ basisForwardConstant Φ := by
  exact norm_nonneg _

/-- The inverse basis constant is at least one. -/
theorem one_le_basisInverseConstant (Φ : E ≃L[ℝ] F) :
    1 ≤ basisInverseConstant Φ := by
  exact le_max_right _ _

/-- The inverse basis constant is strictly positive. -/
theorem basisInverseConstant_pos (Φ : E ≃L[ℝ] F) :
    0 < basisInverseConstant Φ := by
  exact zero_lt_one.trans_le (one_le_basisInverseConstant Φ)

/-- The inverse operator norm is bounded by the canonical inverse constant. -/
theorem inverseNorm_le_basisInverseConstant (Φ : E ≃L[ℝ] F) :
    ‖Φ.symm.toContinuousLinearMap‖ ≤ basisInverseConstant Φ := by
  exact le_max_left _ _

/-- Automatic physical second-order saturation.

No basis constants are supplied by the caller: they are chosen canonically from
the forward and inverse operator norms of the fixed-degree basis equivalence. -/
theorem physical_secondOrder_saturation_automatic
    (Φ : E ≃L[ℝ] F)
    (u v : E) (K : Set E) (L : E →L[ℝ] ℝ)
    (gamma Acoeff Crec h : ℝ)
    (hKcompact : IsCompact K) (hK : K.Nonempty) (hv : v ∈ K)
    (hAcoeff : 0 < Acoeff) (hh : 0 ≤ h)
    (hL : ‖L‖ ≤ Acoeff)
    (hdefect : ∀ w ∈ K, gamma * h ^ 2 ≤ |L (u - w)|)
    (hrecovery : ‖u - v‖ ≤ Crec * h ^ 2) :
    (gamma / (Acoeff * basisInverseConstant Φ)) * h ^ 2 ≤
        bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ∧
      bestApproximationError (Φ u) (transportedFeasibleSet Φ K) ≤
        (basisForwardConstant Φ * Crec) * h ^ 2 := by
  exact physical_secondOrder_saturation_of_basisEquiv
    Φ u v K L gamma Acoeff Crec h
    (basisForwardConstant Φ) (basisInverseConstant Φ)
    hKcompact hK hv hAcoeff hh
    (basisForwardConstant_nonneg Φ) (basisInverseConstant_pos Φ)
    hL hdefect hrecovery le_rfl (inverseNorm_le_basisInverseConstant Φ)

end AutomaticConstants

end

end BernsteinObstacle
