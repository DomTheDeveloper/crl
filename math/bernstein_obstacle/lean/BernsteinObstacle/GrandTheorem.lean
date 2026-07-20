import BernsteinObstacle.GrandSaturationRate

open Filter

namespace BernsteinObstacle

/-!
# Bernstein–Bézier obstacle grand theorem

This terminal theorem packages the complete abstract endgame:

1. threshold-form positive Bernstein/FEM recovery for the zero cone;
2. strongly convergent moving obstacle approximations;
3. Mosco convergence of the translated coefficient cones;
4. strong convergence of the corresponding constrained minimizers once the
   variational-inequality/energy recovery bound vanishes;
5. a sharp three-scale estimate determined by obstacle approximation order,
   bulk approximation order, coefficient consistency, physical vanishing order,
   and defect codimension.

The remaining nonformal inputs are exactly the physical Sobolev/FEM and
free-boundary hypotheses needed to instantiate the data and energy inequalities.
-/

section GrandTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full abstract Bernstein–Bézier obstacle grand theorem.

The rate term is

`h^s + h^r + hGamma^(min(m,q)-1) * sqrt(hGamma^c)`.

Here `s` is the obstacle approximation order, `r` the bulk approximation order,
`m` the coefficient-consistency order, `q` the physical gap-vanishing order,
and `c` the codimension of the defect/free-boundary stratum. -/
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
    (s r m q c : ℕ)
    (he : 0 ≤ e) (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hGammaNonneg : 0 ≤ hGamma)
    (henergy :
      alpha * e ^ 2 ≤
        P * h ^ (2 * s) + A * h ^ (2 * r) +
          B * hGamma ^ (2 * (consistencyLimitedOrder m q - 1) + c)) :
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
      e alpha P A B h hGamma s r m q c
      he halpha hP hA hB hh hGammaNonneg henergy
  exact ⟨hconvergence.1, hconvergence.2, hrate⟩

/-- Quadratic-contact codimension-one specialization.  When `m >= 2`, the
interface contribution saturates at `hGamma * sqrt hGamma`, independently of
higher coefficient consistency. -/
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
