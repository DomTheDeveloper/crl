import BernsteinObstacle.GrandSaturationRate

open Filter

namespace BernsteinObstacle

/-!
# Bernstein–Bézier obstacle grand theorem

This terminal theorem packages threshold-form positive recovery, moving
obstacles, Mosco convergence, minimizer convergence, and the sharp three-scale
rate in the consistency-saturation regime.
-/

section GrandTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bernsteinBezierObstacleGrandTheorem
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
    (s r m q c : ℕ) (hqm : q ≤ m)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hGammaNonneg : 0 ≤ hGamma)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) +
          B * hGamma ^ (2 * (q - 1) + c)) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r +
          consistencyVanishingCodimensionScale hGamma m q c) := by
  have hconvergence :=
    D.movingObstacle_minimizers_strongConvergence
      psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
  have hrate :=
    grandSharpRate_of_consistencyLimitedComponents
      e alpha P A B h hGamma s r m q c hqm
      he halpha hP hA hB hh hGammaNonneg henergy
  exact ⟨hconvergence.1, hconvergence.2, hrate⟩

theorem bernsteinBezierObstacleGrandTheorem_quadraticContact
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
    (s r m : ℕ) (hm : 2 ≤ m)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hGammaNonneg : 0 ≤ hGamma)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) + B * hGamma ^ 3) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r + hGamma * Real.sqrt hGamma) := by
  have hconvergence :=
    D.movingObstacle_minimizers_strongConvergence
      psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
  have hrate :=
    grandSharpRate_quadraticContact_saturation
      e alpha P A B h hGamma s r m hm
      he halpha hP hA hB hh hGammaNonneg henergy
  exact ⟨hconvergence.1, hconvergence.2, hrate⟩

end GrandTheorem

end BernsteinObstacle
