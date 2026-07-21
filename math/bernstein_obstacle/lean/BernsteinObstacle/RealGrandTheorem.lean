import BernsteinObstacle.GrandTheorem
import BernsteinObstacle.RealMinkowskiClassification
import Mathlib.Tactic

open Filter

namespace BernsteinObstacle

section RealGrandTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Three-component coercive transfer with the fractional Minkowski rate scale. -/
theorem grandSharpRate_of_realMinkowskiComponents
    (e alpha P A B h g : ℝ) (s r : ℕ) (m q c : ℝ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      alpha * e ^ 2 ≤
        P * (h ^ s) ^ 2 + A * (h ^ r) ^ 2 +
          B * (realVIRateScale g m q c) ^ 2) :
    e ≤ Real.sqrt (max P (max A B) / alpha) *
      (h ^ s + h ^ r + realVIRateScale g m q c) := by
  apply sharpRate_of_three_components
    e alpha P A B (h ^ s) (h ^ r) (realVIRateScale g m q c)
      he halpha hP hA hB
  · exact pow_nonneg hh _
  · exact pow_nonneg hh _
  · unfold realVIRateScale
    exact Real.rpow_nonneg hg _
  · exact henergy

/-- Terminal grand theorem with arbitrary real consistency, vanishing, and
 tubular-volume exponents. -/
theorem bernsteinBezierObstacleGrandTheorem_realMinkowski
    (D : ThresholdSobolevFEMRecoveryData E)
    (psi_h : ℕ → E) (psi : E)
    (hpsi : StronglyConverges psi_h psi)
    (x : E) (hx : x ∈ obstacleCone psi D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ recovery : ℕ → E,
        (∀ n, recovery n ∈ movingObstacleCone psi_h D.discreteCone n) →
        StronglyConverges recovery x →
        ∀ n, ‖u n - recovery n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0))
    (e alpha P A B h hGamma : ℝ)
    (s r : ℕ) (m q c : ℝ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hGammaNonneg : 0 ≤ hGamma)
    (henergy :
      alpha * e ^ 2 ≤
        P * (h ^ s) ^ 2 + A * (h ^ r) ^ 2 +
          B * (realVIRateScale hGamma m q c) ^ 2) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r + realVIRateScale hGamma m q c) := by
  have hconvergence :=
    D.movingObstacle_minimizers_strongConvergence
      psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
  have hrate :=
    grandSharpRate_of_realMinkowskiComponents
      e alpha P A B h hGamma s r m q c
      he halpha hP hA hB hh hGammaNonneg henergy
  exact ⟨hconvergence.1, hconvergence.2, hrate⟩

/-- Consistency-limited terminal theorem for the fractional regime `m ≤ q`. -/
theorem bernsteinBezierObstacleGrandTheorem_consistencyLimited
    (D : ThresholdSobolevFEMRecoveryData E)
    (psi_h : ℕ → E) (psi : E)
    (hpsi : StronglyConverges psi_h psi)
    (x : E) (hx : x ∈ obstacleCone psi D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ recovery : ℕ → E,
        (∀ n, recovery n ∈ movingObstacleCone psi_h D.discreteCone n) →
        StronglyConverges recovery x →
        ∀ n, ‖u n - recovery n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0))
    (e alpha P A B h hGamma : ℝ)
    (s r : ℕ) (m q c : ℝ)
    (hmq : m ≤ q) (hq : 0 < q) (hm2 : 2 ≤ m)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hGammaNonneg : 0 ≤ hGamma)
    (henergy :
      alpha * e ^ 2 ≤
        P * (h ^ s) ^ 2 + A * (h ^ r) ^ 2 +
          B * (hGamma ^ (m / 2 * (1 + c / q))) ^ 2) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r + hGamma ^ (m / 2 * (1 + c / q))) := by
  rw [← realVIRateScale_of_m_le_q hGamma m q c hmq hq hm2] at henergy ⊢
  exact bernsteinBezierObstacleGrandTheorem_realMinkowski
    D psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c
    he halpha hP hA hB hh hGammaNonneg henergy

/-- Saturation-regime real-power terminal theorem. -/
theorem bernsteinBezierObstacleGrandTheorem_saturatedReal
    (D : ThresholdSobolevFEMRecoveryData E)
    (psi_h : ℕ → E) (psi : E)
    (hpsi : StronglyConverges psi_h psi)
    (x : E) (hx : x ∈ obstacleCone psi D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ recovery : ℕ → E,
        (∀ n, recovery n ∈ movingObstacleCone psi_h D.discreteCone n) →
        StronglyConverges recovery x →
        ∀ n, ‖u n - recovery n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0))
    (e alpha P A B h hGamma : ℝ)
    (s r : ℕ) (m q c : ℝ)
    (hqm : q ≤ m) (hq : 0 < q) (hq2 : 2 ≤ q)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hGammaNonneg : 0 ≤ hGamma)
    (henergy :
      alpha * e ^ 2 ≤
        P * (h ^ s) ^ 2 + A * (h ^ r) ^ 2 +
          B * (hGamma ^ ((q + c) / 2)) ^ 2) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r + hGamma ^ ((q + c) / 2)) := by
  rw [← realVIRateScale_of_q_le_m hGamma m q c hqm hq hq2] at henergy ⊢
  exact bernsteinBezierObstacleGrandTheorem_realMinkowski
    D psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c
    he halpha hP hA hB hh hGammaNonneg henergy

end RealGrandTheorem

end BernsteinObstacle
