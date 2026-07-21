import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Aligned-mesh obstruction

A positive mesh-independent `h^(3/2)` lower bound cannot hold for all
shape-regular quadratic meshes.  When the free boundary is part of the mesh
skeleton, the half-quadratic profile is represented exactly: it is zero on one
side and a quadratic polynomial on the other, with matching trace at the
interface.
-/

def halfQuadraticProfile (a y : ℝ) : ℝ :=
  a * (max y 0) ^ 2

theorem halfQuadraticProfile_of_nonpos
    (a y : ℝ) (hy : y ≤ 0) :
    halfQuadraticProfile a y = 0 := by
  simp [halfQuadraticProfile, max_eq_right hy]

theorem halfQuadraticProfile_of_nonneg
    (a y : ℝ) (hy : 0 ≤ y) :
    halfQuadraticProfile a y = a * y ^ 2 := by
  simp [halfQuadraticProfile, max_eq_left hy]

theorem halfQuadraticProfile_at_interface (a : ℝ) :
    halfQuadraticProfile a 0 = 0 := by
  simp [halfQuadraticProfile]

theorem continuous_halfQuadraticProfile (a : ℝ) :
    Continuous (halfQuadraticProfile a) := by
  unfold halfQuadraticProfile
  fun_prop

theorem exactRepresentability_refutes_positiveLowerBound
    {E : Type*} [NormedAddCommGroup E]
    (V : Set E) (u : E) (hu : u ∈ V)
    (c h : ℝ) (hc : 0 < c) (hh : 0 < h) :
    ¬ (∀ v ∈ V, c * (h * Real.sqrt h) ≤ ‖u - v‖) := by
  intro hall
  have hself := hall u hu
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have htarget : 0 < c * (h * Real.sqrt h) := by positivity
  have hzero : ‖u - u‖ = 0 := by simp
  rw [hzero] at hself
  linarith

def quadraticContactPhaseWeight (theta : ℝ) : ℝ :=
  theta ^ 3 * (1 - theta) ^ 3

@[simp] theorem quadraticContactPhaseWeight_zero :
    quadraticContactPhaseWeight 0 = 0 := by
  simp [quadraticContactPhaseWeight]

@[simp] theorem quadraticContactPhaseWeight_one :
    quadraticContactPhaseWeight 1 = 0 := by
  simp [quadraticContactPhaseWeight]

theorem quadraticContactPhaseWeight_tendsto_zero
    {ι : Type*} {l : Filter ι} (theta : ι → ℝ)
    (htheta : Filter.Tendsto theta l (nhds 0)) :
    Filter.Tendsto (fun i => quadraticContactPhaseWeight (theta i)) l (nhds 0) := by
  have hcont : Continuous quadraticContactPhaseWeight := by
    unfold quadraticContactPhaseWeight
    fun_prop
  change Filter.Tendsto (quadraticContactPhaseWeight ∘ theta) l (nhds 0)
  have hlimit := hcont.continuousAt.tendsto.comp htheta
  simpa using hlimit

theorem quadraticContactPhaseCoefficient_tendsto_zero
    {ι : Type*} {l : Filter ι} (theta : ι → ℝ)
    (htheta : Filter.Tendsto theta l (nhds 0)) :
    Filter.Tendsto
      (fun i => Real.sqrt (quadraticContactPhaseWeight (theta i))) l
      (nhds 0) := by
  have hweight := quadraticContactPhaseWeight_tendsto_zero theta htheta
  have hsqrt : Continuous Real.sqrt := Real.continuous_sqrt
  change Filter.Tendsto
    (Real.sqrt ∘ fun i => quadraticContactPhaseWeight (theta i)) l (nhds 0)
  have hlimit := hsqrt.continuousAt.tendsto.comp hweight
  simpa using hlimit

end BernsteinObstacle
