import BernsteinObstacle.AssembledObstacle
import BernsteinObstacle.AsymptoticGrandTheorem
import BernsteinObstacle.CoefficientClearance

open Filter

namespace BernsteinObstacle

/-!
# Concrete assembled-mesh Bernstein obstacle grand theorem

This file specializes the abstract clearance recovery theorem to the actual
`BernsteinAssembly` feasible set of globally shared coefficients.  The finite
certificate distinguishes movable degrees of freedom from trace-fixed degrees
of freedom:

* free global coefficients have a strict positive margin;
* the FEM coefficient recovery converges in the finite sup norm;
* non-free coefficients are certified nonnegative separately;
* every designated boundary coefficient is exactly zero.

Consequently the recovery belongs to the assembled feasible set for all
sufficiently fine meshes.  The result then enters the existing diagonal,
Mosco, moving-obstacle, minimizer, and sharp-rate theorem chain.
-/

noncomputable section

section AssembledRecovery

variable {Element Dof : Type*} [Fintype Dof] {d p : ℕ}

/-- Physical recovery data for a sequence of conforming Bernstein assemblies
with a fixed global coefficient space. -/
structure AssembledFreeCoefficientRecoveryData
    (Element Dof : Type*) [Fintype Dof] (d p : ℕ) where
  assembly : ℕ → BernsteinAssembly Element Dof d p
  limitCone : Set (Dof → ℝ)
  smoothApprox : (Dof → ℝ) → ℕ → Dof → ℝ
  femRecovery : (Dof → ℝ) → ℕ → ℕ → Dof → ℝ
  clearance : (Dof → ℝ) → ℕ → ℝ
  freeDof : ℕ → Set Dof
  smooth_converges :
    ∀ x, x ∈ limitCone → StronglyConverges (smoothApprox x) x
  zero_recovery_mem :
    ∀ x, x ∈ limitCone → ∀ n,
      femRecovery x 0 n ∈ assemblyFeasibleSet (assembly n)
  zero_recovery_close :
    ∀ x, x ∈ limitCone → ∀ n,
      ‖femRecovery x 0 n - smoothApprox x 0‖ ≤ (1 : ℝ)
  clearance_pos :
    ∀ x, x ∈ limitCone → ∀ m, 0 < clearance x m
  recovery_tendsto :
    ∀ x, x ∈ limitCone → ∀ m,
      Tendsto (fun n => femRecovery x m n - smoothApprox x m)
        atTop (nhds 0)
  free_margin :
    ∀ x, x ∈ limitCone → ∀ m n i,
      i ∈ freeDof n → clearance x m ≤ smoothApprox x m i
  nonfree_nonneg :
    ∀ x, x ∈ limitCone → ∀ m n i,
      i ∉ freeDof n → 0 ≤ femRecovery x m n i
  boundary_zero :
    ∀ x, x ∈ limitCone → ∀ m n i,
      i ∈ (assembly n).boundaryDof → femRecovery x m n i = 0
  inner :
    ∀ n, assemblyFeasibleSet (assembly n) ⊆ limitCone
  limit_convex : Convex ℝ limitCone
  limit_closed : IsClosed limitCone

/-- A recovery error below the free-coefficient margin gives exact assembled
feasibility: global Bernstein nonnegativity and homogeneous boundary values. -/
theorem AssembledFreeCoefficientRecoveryData.recovery_mem_of_norm_lt_clearance
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (x : Dof → ℝ) (hx : x ∈ D.limitCone)
    (m n : ℕ)
    (hclose : ‖D.femRecovery x m n - D.smoothApprox x m‖ < D.clearance x m) :
    D.femRecovery x m n ∈ assemblyFeasibleSet (D.assembly n) := by
  constructor
  · exact mem_coefficientCone_of_margin_on_free_of_norm_sub_lt
      (D.freeDof n) (D.smoothApprox x m) (D.femRecovery x m n)
      (D.clearance x m) (D.clearance_pos x hx m)
      (D.free_margin x hx m n) (D.nonfree_nonneg x hx m n) hclose
  · exact D.boundary_zero x hx m n

/-- Convert assembled free-coefficient recovery data into the generic strict-
clearance recovery interface. -/
def AssembledFreeCoefficientRecoveryData.toClearanceData
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p) :
    ClearanceSobolevFEMRecoveryData (Dof → ℝ) where
  discreteCone := fun n => assemblyFeasibleSet (D.assembly n)
  limitCone := D.limitCone
  smoothApprox := D.smoothApprox
  femRecovery := D.femRecovery
  clearance := D.clearance
  smooth_converges := D.smooth_converges
  zero_recovery_mem := D.zero_recovery_mem
  zero_recovery_close := D.zero_recovery_close
  clearance_pos := D.clearance_pos
  recovery_tendsto := D.recovery_tendsto
  recovery_mem_of_norm_lt_clearance := by
    intro x hx m n hclose
    exact D.recovery_mem_of_norm_lt_clearance x hx m n hclose
  inner := D.inner
  limit_convex := D.limit_convex
  limit_closed := D.limit_closed

/-- Assembled free-coefficient recovery implies Mosco convergence of the actual
assembled feasible sets. -/
theorem AssembledFreeCoefficientRecoveryData.moscoConverges
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p) :
    MoscoConverges
      (fun n => assemblyFeasibleSet (D.assembly n)) D.limitCone := by
  exact D.toClearanceData.moscoConverges

/-- Assembled free-coefficient recovery implies strong convergence of the
constrained minimizers under the standard comparison estimate. -/
theorem AssembledFreeCoefficientRecoveryData.minimizers_strongConvergence
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (x : Dof → ℝ) (hx : x ∈ D.limitCone)
    (u : ℕ → Dof → ℝ) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ recovery : ℕ → Dof → ℝ,
        (∀ n, recovery n ∈ assemblyFeasibleSet (D.assembly n)) →
        StronglyConverges recovery x →
        ∀ n, ‖u n - recovery n‖ ≤ solutionErr n)
    (hsolutionErr : Tendsto solutionErr atTop (nhds 0)) :
    MoscoConverges
        (fun n => assemblyFeasibleSet (D.assembly n)) D.limitCone ∧
      StronglyConverges u x := by
  exact D.toClearanceData.minimizers_strongConvergence
    x hx u solutionErr hsolution hsolutionErr

end AssembledRecovery

section AssembledMovingGrandTheorem

variable {Element Dof : Type*} [Fintype Dof] {d p : ℕ}

/-- Moving-obstacle Mosco convergence for the actual assembled Bernstein
feasible sets. -/
theorem AssembledFreeCoefficientRecoveryData.movingObstacle_moscoConverges
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (psi_h : ℕ → Dof → ℝ) (psi : Dof → ℝ)
    (hpsi : StronglyConverges psi_h psi) :
    MoscoConverges
      (movingObstacleCone psi_h
        (fun n => assemblyFeasibleSet (D.assembly n)))
      (obstacleCone psi D.limitCone) := by
  exact D.toClearanceData.movingObstacle_moscoConverges psi_h psi hpsi

/-- Complete assembled Bernstein–Bézier grand theorem from free-coefficient
clearance, exact boundary traces, FEM convergence, and the terminal energy
inequality. -/
theorem AssembledFreeCoefficientRecoveryData.bernsteinBezierObstacleGrandTheorem
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (psi_h : ℕ → Dof → ℝ) (psi : Dof → ℝ)
    (hpsi : StronglyConverges psi_h psi)
    (x : Dof → ℝ) (hx : x ∈ obstacleCone psi D.limitCone)
    (u : ℕ → Dof → ℝ) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ recovery : ℕ → Dof → ℝ,
        (∀ n, recovery n ∈ movingObstacleCone psi_h
          (fun k => assemblyFeasibleSet (D.assembly k)) n) →
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
        (movingObstacleCone psi_h
          (fun n => assemblyFeasibleSet (D.assembly n)))
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r +
          consistencyVanishingCodimensionScale hGamma m q c) := by
  exact D.toClearanceData.bernsteinBezierObstacleGrandTheorem
    psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m q c hqm
    he halpha hP hA hB hh hGammaNonneg henergy

/-- Sharp quadratic codimension-one assembled theorem with contact contribution
`hGamma * sqrt hGamma`. -/
theorem AssembledFreeCoefficientRecoveryData.bernsteinBezierObstacleGrandTheorem_quadraticContact
    (D : AssembledFreeCoefficientRecoveryData Element Dof d p)
    (psi_h : ℕ → Dof → ℝ) (psi : Dof → ℝ)
    (hpsi : StronglyConverges psi_h psi)
    (x : Dof → ℝ) (hx : x ∈ obstacleCone psi D.limitCone)
    (u : ℕ → Dof → ℝ) (solutionErr : ℕ → ℝ)
    (hsolution :
      ∀ recovery : ℕ → Dof → ℝ,
        (∀ n, recovery n ∈ movingObstacleCone psi_h
          (fun k => assemblyFeasibleSet (D.assembly k)) n) →
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
        (movingObstacleCone psi_h
          (fun n => assemblyFeasibleSet (D.assembly n)))
        (obstacleCone psi D.limitCone) ∧
      StronglyConverges u x ∧
      e ≤ Real.sqrt (max P (max A B) / alpha) *
        (h ^ s + h ^ r + hGamma * Real.sqrt hGamma) := by
  exact D.toClearanceData.bernsteinBezierObstacleGrandTheorem_quadraticContact
    psi_h psi hpsi x hx u solutionErr hsolution hsolutionErr
    e alpha P A B h hGamma s r m hm
    he halpha hP hA hB hh hGammaNonneg henergy

end AssembledMovingGrandTheorem

end
end BernsteinObstacle
