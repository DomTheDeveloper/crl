import BernsteinObstacle.DesignedTubularMesh
import BernsteinObstacle.WeightedPrismSaturation
import Mathlib.Tactic

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

/-!
# Explicit curved-interface threshold

For positive curvature bound `K` and transverse half-width factor `c`, the
concrete threshold `h₀ = 1 / (2 K c)` guarantees both the phase margin and the
Jacobian lower bound. At that threshold the mapped transverse-prism theorem
has the explicit local coefficient `a² M / 6144`.
-/

def curvedMeshThreshold (K c : ℝ) : ℝ :=
  1 / (2 * K * c)

theorem curvedMeshThreshold_pos
    (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    0 < curvedMeshThreshold K c := by
  unfold curvedMeshThreshold
  positivity

theorem curvedMeshThreshold_implies_smallness
    (K c h : ℝ) (hK : 0 < K) (hc : 0 < c)
    (_hh : 0 ≤ h) (hthreshold : h ≤ curvedMeshThreshold K c) :
    K * c * h ≤ 1 / 2 := by
  have hKc : 0 ≤ K * c := (mul_pos hK hc).le
  calc
    K * c * h ≤ K * c * curvedMeshThreshold K c :=
      mul_le_mul_of_nonneg_left hthreshold hKc
    _ = 1 / 2 := by
      unfold curvedMeshThreshold
      field_simp [ne_of_gt hK, ne_of_gt hc]

theorem curvedMeshThreshold_phase_and_jacobian
    (K c h delta k t : ℝ)
    (hK : 0 < K) (hc : 0 < c) (hh : 0 < h)
    (hthreshold : h ≤ curvedMeshThreshold K c)
    (hdelta : |delta| ≤ K * (c * h) ^ 2 / 2)
    (hk : |k| ≤ K) (ht : |t| ≤ c * h) :
    ((1 / 4 : ℝ) ≤ (delta + c * h) / (2 * c * h) ∧
      (delta + c * h) / (2 * c * h) ≤ 3 / 4) ∧
    ((1 / 2 : ℝ) ≤ 1 - t * k ∧ 1 - t * k ≤ 3 / 2) := by
  have hsmallHalf := curvedMeshThreshold_implies_smallness
    K c h hK hc hh.le hthreshold
  have hsmallOne : K * c * h ≤ 1 := hsmallHalf.trans (by norm_num)
  exact ⟨
    curvedFiber_phase_bounds K c h delta hK.le hc hh hsmallOne hdelta,
    curvedFiber_jacobian_bounds K c h k t hK.le hc.le hh.le hk ht hsmallHalf
  ⟩

/-- At the explicit threshold, a curved mapped prism has the exact local ideal
energy coefficient `a² M / 6144`. -/
theorem curvedWeightedPrism_integral_lowerBound_explicit
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude K c h delta M : ℝ) (d : ℕ)
    (alpha beta t k : Y → ℝ)
    (hK : 0 < K) (hc : 0 < c) (hh : 0 < h)
    (hM : 0 ≤ M) (hd : 1 ≤ d)
    (hthreshold : h ≤ curvedMeshThreshold K c)
    (hdelta : |delta| ≤ K * (c * h) ^ 2 / 2)
    (ht : ∀ y, |t y| ≤ c * h)
    (hk : ∀ y, |k y| ≤ K)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hIntegrable : Integrable
      (fun y => (1 - t y * k y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta + c * h) / (2 * c * h))
          (alpha y) (beta y)) μ) :
    (amplitude ^ 2 * M / 6144) * h ^ (d + 2) ≤
      ∫ y, (1 - t y * k y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta + c * h) / (2 * c * h))
          (alpha y) (beta y) ∂μ := by
  have hsmallHalf := curvedMeshThreshold_implies_smallness
    K c h hK hc hh.le hthreshold
  have hsmallOne : K * c * h ≤ 1 := hsmallHalf.trans (by norm_num)
  have hphase := curvedFiber_phase_bounds
    K c h delta hK.le hc hh hsmallOne hdelta
  have hright :
      (delta + c * h) / (2 * c * h) ≤ 1 - (1 / 4 : ℝ) := by
    norm_num
    exact hphase.2
  have hJacobian : ∀ y, (1 / 2 : ℝ) ≤ 1 - t y * k y := by
    intro y
    exact (curvedFiber_jacobian_bounds
      K c h (k y) (t y) hK.le hc.le hh.le (hk y) (ht y) hsmallHalf).1
  have hlower := weightedTransversePrism_localEnergy_lowerBound
    μ amplitude h ((delta + c * h) / (2 * c * h)) (1 / 4) M (1 / 2) d
    alpha beta (fun y => 1 - t y * k y)
    hd hh.le (by norm_num) hM (by norm_num)
    hphase.1 hright hMass hJacobian hIntegrable
  have hcoefficient :
      (amplitude ^ 2 * M / 6144) * h ^ (d + 2) =
        ((1 / 2 : ℝ) *
          (((4 : ℝ) / 3) * amplitude ^ 2 * (1 / 4 : ℝ) ^ 6 * M)) *
            h ^ (d + 2) := by
    ring
  rw [hcoefficient]
  exact hlower

/-- Physical local-energy form of the explicit curved coefficient. -/
theorem curvedWeightedPrism_localEnergy_lowerBound_explicit
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude K c h delta M localEnergy : ℝ) (d : ℕ)
    (alpha beta t k : Y → ℝ)
    (hK : 0 < K) (hc : 0 < c) (hh : 0 < h)
    (hM : 0 ≤ M) (hd : 1 ≤ d)
    (hthreshold : h ≤ curvedMeshThreshold K c)
    (hdelta : |delta| ≤ K * (c * h) ^ 2 / 2)
    (ht : ∀ y, |t y| ≤ c * h)
    (hk : ∀ y, |k y| ≤ K)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hIntegrable : Integrable
      (fun y => (1 - t y * k y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta + c * h) / (2 * c * h))
          (alpha y) (beta y)) μ)
    (hLocalDominates :
      (∫ y, (1 - t y * k y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta + c * h) / (2 * c * h))
          (alpha y) (beta y) ∂μ) ≤ localEnergy) :
    (amplitude ^ 2 * M / 6144) * h ^ (d + 2) ≤ localEnergy := by
  exact (curvedWeightedPrism_integral_lowerBound_explicit
    μ amplitude K c h delta M d alpha beta t k
    hK hc hh hM hd hthreshold hdelta ht hk hMass hIntegrable).trans
    hLocalDominates

end

end BernsteinObstacle
