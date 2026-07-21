import BernsteinObstacle.AsymptoticGrandTheorem
import BernsteinObstacle.RealGrandTheorem

open Filter

namespace BernsteinObstacle

section FullGrandFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AsymptoticSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem_realMinkowski
    (D : AsymptoticSobolevFEMRecoveryData E)
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
  exact bernsteinBezierObstacleGrandTheorem_realMinkowski
    D.toThresholdData psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c
    he halpha hP hA hB hh hGammaNonneg henergy

theorem AsymptoticSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem_consistencyLimited
    (D : AsymptoticSobolevFEMRecoveryData E)
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
  exact bernsteinBezierObstacleGrandTheorem_consistencyLimited
    D.toThresholdData psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c hmq hq hm2
    he halpha hP hA hB hh hGammaNonneg henergy

theorem ClearanceSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem_realMinkowski
    (D : ClearanceSobolevFEMRecoveryData E)
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
  exact D.toAsymptoticData.bernsteinBezierObstacleGrandTheorem_realMinkowski
    psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c
    he halpha hP hA hB hh hGammaNonneg henergy

theorem ClearanceSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem_consistencyLimited
    (D : ClearanceSobolevFEMRecoveryData E)
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
  exact D.toAsymptoticData.bernsteinBezierObstacleGrandTheorem_consistencyLimited
    psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c hmq hq hm2
    he halpha hP hA hB hh hGammaNonneg henergy

end FullGrandFormalization

end BernsteinObstacle
