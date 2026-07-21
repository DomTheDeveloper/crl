import BernsteinObstacle.AsymptoticRecovery
import BernsteinObstacle.GrandTheorem

open Filter

namespace BernsteinObstacle

/-!
# Ordinary FEM convergence implies the Bernstein–Bézier grand theorem

The canonical terminal theorem is phrased using explicit recovery thresholds.
A physical finite-element argument normally supplies the more natural facts that,
for every fixed smooth recovery stage, feasibility holds eventually and the
recovery error tends to zero as the mesh is refined.

`AsymptoticSobolevFEMRecoveryData.toThresholdData` already extracts the required
threshold schedule.  This file closes the final composition gap: the ordinary
asymptotic FEM hypotheses now feed directly into moving-obstacle Mosco
convergence, strong minimizer convergence, and both terminal grand-rate
theorems.
-/

section AsymptoticMovingObstacle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordinary fixed-stage FEM convergence is sufficient for Mosco convergence of
moving obstacle cones; no threshold schedule needs to be supplied by the user. -/
theorem AsymptoticSobolevFEMRecoveryData.movingObstacle_moscoConverges
    (D : AsymptoticSobolevFEMRecoveryData E)
    (psi_h : ℕ → E) (psi : E)
    (hpsi : StronglyConverges psi_h psi) :
    MoscoConverges
      (movingObstacleCone psi_h D.discreteCone)
      (obstacleCone psi D.limitCone) := by
  exact D.toThresholdData.movingObstacle_moscoConverges psi_h psi hpsi

/-- Ordinary fixed-stage FEM convergence closes the moving-obstacle minimizer
endgame after the usual recovery-comparison estimate. -/
theorem AsymptoticSobolevFEMRecoveryData.movingObstacle_minimizers_strongConvergence
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
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x := by
  exact D.toThresholdData.movingObstacle_minimizers_strongConvergence
    psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr

end AsymptoticMovingObstacle

section AsymptoticGrandTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The terminal Bernstein–Bézier obstacle grand theorem under the ordinary
finite-element hypotheses: eventual feasibility and fixed-stage recovery error
tending to zero.  Explicit diagonal thresholds are extracted internally. -/
theorem AsymptoticSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem
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
  exact BernsteinObstacle.bernsteinBezierObstacleGrandTheorem
    D.toThresholdData psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c hqm
    he halpha hP hA hB hh hGammaNonneg henergy

/-- Quadratic codimension-one specialization of the asymptotic grand theorem,
with the sharp `hGamma * sqrt hGamma` contact term. -/
theorem AsymptoticSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem_quadraticContact
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
  exact BernsteinObstacle.bernsteinBezierObstacleGrandTheorem_quadraticContact
    D.toThresholdData psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m hm
    he halpha hP hA hB hh hGammaNonneg henergy

end AsymptoticGrandTheorem

end BernsteinObstacle
