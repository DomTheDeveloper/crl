import BernsteinObstacle.SobolevFEMRecovery
import BernsteinObstacle.TranslatedMosco

open Filter

namespace BernsteinObstacle

section MovingObstacleConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def movingObstacleCone
    (psi_h : ℕ → E) (K : ℕ → Set E) (n : ℕ) : Set E :=
  translatedSet (psi_h n) (K n)

def obstacleCone (psi : E) (K : Set E) : Set E :=
  translatedSet psi K

@[simp]
theorem mem_movingObstacleCone
    {psi_h : ℕ → E} {K : ℕ → Set E} {n : ℕ} {u : E} :
    u ∈ movingObstacleCone psi_h K n ↔ u - psi_h n ∈ K n :=
  Iff.rfl

@[simp]
theorem mem_obstacleCone
    {psi : E} {K : Set E} {u : E} :
    u ∈ obstacleCone psi K ↔ u - psi ∈ K :=
  Iff.rfl

theorem ThresholdSobolevFEMRecoveryData.movingObstacle_moscoConverges
    (D : ThresholdSobolevFEMRecoveryData E)
    (psi_h : ℕ → E) (psi : E)
    (hpsi : StronglyConverges psi_h psi) :
    MoscoConverges
      (movingObstacleCone psi_h D.discreteCone)
      (obstacleCone psi D.limitCone) := by
  exact moscoConverges_translated
    D.discreteCone D.limitCone psi_h psi D.moscoConverges hpsi

theorem ThresholdSobolevFEMRecoveryData.movingObstacle_minimizers_strongConvergence
    (D : ThresholdSobolevFEMRecoveryData E)
    (psi_h : ℕ → E) (psi : E)
    (hpsi : StronglyConverges psi_h psi)
    (x : E) (hx : x ∈ obstacleCone psi D.limitCone)
    (u : ℕ → E) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ r : ℕ → E,
        (∀ n, r n ∈ movingObstacleCone psi_h D.discreteCone n) →
        StronglyConverges r x →
        ∀ n, ‖u n - r n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x := by
  have hM :
      MoscoConverges
        (movingObstacleCone psi_h D.discreteCone)
        (obstacleCone psi D.limitCone) :=
    D.movingObstacle_moscoConverges psi_h psi hpsi
  refine ⟨hM, ?_⟩
  exact mosco_recovery_closeness_implies_strong_convergence
    hM x hx u solutionErr hsolution hsolutionErr

theorem ThresholdSobolevFEMRecoveryData.fixedObstacle_moscoConverges
    (D : ThresholdSobolevFEMRecoveryData E)
    (psi : E) :
    MoscoConverges
      (movingObstacleCone (fun _ => psi) D.discreteCone)
      (obstacleCone psi D.limitCone) := by
  exact D.movingObstacle_moscoConverges
    (fun _ => psi) psi tendsto_const_nhds

end MovingObstacleConvergence

end BernsteinObstacle
