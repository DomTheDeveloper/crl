import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Minimal Sobolev `H₀¹` port for the Bernstein obstacle recovery theorem

The external De Giorgi development used during exploration is pinned to an
older Lean/mathlib release.  This file ports only the definitions and positive-
part `L²` infrastructure needed by the Bernstein recovery argument to the
project's current pinned stack.

It deliberately avoids importing the incompatible package graph.  The port
contains:

* weak partial derivatives and weak gradients;
* `W^{1,p}`, explicit weak-gradient witnesses, `W₀^{1,p}`, and `H₀¹`;
* extraction of the smooth compactly supported approximation sequence already
  contained in `H₀¹` membership;
* the positive-part gradient candidate and its componentwise `L²` bound;
* a reusable nonnegative smooth-density witness which packages the exact
  analytical input needed by the obstacle recovery layer.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace BernsteinObstacle
namespace SobolevH01Port

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Weak partial derivative on an open set, copied onto the current project
stack so the Bernstein development does not depend on the old De Giorgi pin. -/
def HasWeakPartialDeriv (i : Fin d) (g f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ φ : E → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, g x * φ x

/-- Weak gradient assembled from the weak partial derivatives. -/
def HasWeakGrad (G : E → E) (f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ i : Fin d, HasWeakPartialDeriv i (fun x => G x i) f Ω

/-- Membership in `W^{1,p}(Ω)`. -/
def MemW1p (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) : Prop :=
  MemLp f p (μ.restrict Ω) ∧
    ∀ i : Fin d, ∃ g : E → ℝ,
      MemLp g p (μ.restrict Ω) ∧ HasWeakPartialDeriv i g f Ω

/-- An explicit weak-gradient witness for `W^{1,p}` membership. -/
structure MemW1pWitness (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) where
  memLp : MemLp f p (μ.restrict Ω)
  weakGrad : E → E
  weakGrad_component_memLp : ∀ i : Fin d,
    MemLp (fun x => weakGrad x i) p (μ.restrict Ω)
  isWeakGrad : HasWeakGrad weakGrad f Ω

/-- Forget the explicit weak-gradient witness. -/
theorem MemW1pWitness.memW1p
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemW1p p f Ω μ := by
  refine ⟨hw.memLp, ?_⟩
  intro i
  exact ⟨fun x => hw.weakGrad x i,
    hw.weakGrad_component_memLp i, hw.isWeakGrad i⟩

/-- `H¹(Ω) = W^{1,2}(Ω)`. -/
abbrev MemH1 (f : E → ℝ) (Ω : Set E) (μ : Measure E := volume) :=
  MemW1p 2 f Ω μ

/-- Zero-trace Sobolev membership via smooth compactly supported approximation
in both the function and weak-gradient `Lᵖ` errors. -/
def MemW01p (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) : Prop :=
  MemW1p p f Ω μ ∧
    ∃ (hw : MemW1pWitness p f Ω μ) (φ : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - f x) p (μ.restrict Ω))
        atTop (nhds 0) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i)
          p (μ.restrict Ω)) atTop (nhds 0)

/-- `H₀¹(Ω) = W₀^{1,2}(Ω)`. -/
abbrev MemH01 (f : E → ℝ) (Ω : Set E) (μ : Measure E := volume) :=
  MemW01p 2 f Ω μ

/-- Extract the smooth compactly supported approximation data encoded by an
`H₀¹` proof. -/
theorem smoothApproxData_of_memH01
    {Ω : Set E} {u : E → ℝ}
    (hu : MemH01 u Ω) :
    ∃ (hw : MemW1pWitness 2 u Ω) (φ : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2
        (volume.restrict Ω)) atTop (nhds 0) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i)
          2 (volume.restrict Ω)) atTop (nhds 0) := by
  simpa [MemH01, MemW01p] using hu.2

/-- Pointwise positive part. -/
def positivePart (u : E → ℝ) : E → ℝ := fun x => max (u x) 0

@[simp]
theorem positivePart_nonneg (u : E → ℝ) (x : E) :
    0 ≤ positivePart u x := by
  simp [positivePart]

@[simp]
theorem positivePart_eq_self {u : E → ℝ} {x : E} (hx : 0 ≤ u x) :
    positivePart u x = u x := by
  simp [positivePart, max_eq_left hx]

@[simp]
theorem positivePart_eq_zero {u : E → ℝ} {x : E} (hx : u x ≤ 0) :
    positivePart u x = 0 := by
  simp [positivePart, max_eq_right hx]

/-- The canonical positive-part weak-gradient candidate. -/
def positivePartGrad {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) : E → E :=
  fun x => if 0 < u x then hw.weakGrad x else 0

omit [NeZero d] in
/-- Truncating an `L²` function by the positivity set of an a.e.-measurable
scalar function preserves `L²`. -/
theorem indicator_component_memLp
    {Ω : Set E} {σ g : E → ℝ}
    (hσ_aemeas : AEMeasurable σ (volume.restrict Ω))
    (hg_memLp : MemLp g 2 (volume.restrict Ω)) :
    MemLp (fun x => if 0 < σ x then g x else 0) 2
      (volume.restrict Ω) := by
  let h : ℝ × ℝ → ℝ := fun yz => if 0 < yz.1 then yz.2 else 0
  have hh_meas : Measurable h := by
    refine measurable_snd.piecewise ?_ measurable_const
    exact measurableSet_lt measurable_const measurable_fst
  have hpair_aemeas :
      AEMeasurable (fun x => (σ x, g x)) (volume.restrict Ω) :=
    hσ_aemeas.prodMk hg_memLp.aemeasurable
  have htrunc_aestrong :
      AEStronglyMeasurable (fun x => if 0 < σ x then g x else 0)
        (volume.restrict Ω) := by
    refine (hh_meas.comp_aemeasurable hpair_aemeas).aestronglyMeasurable.congr ?_
    filter_upwards [] with x
    by_cases hx : 0 < σ x <;> simp [h, hx]
  refine hg_memLp.norm.mono' htrunc_aestrong ?_
  filter_upwards [] with x
  by_cases hx : 0 < σ x <;> simp [hx]

/-- Every component of the positive-part gradient candidate belongs to `L²`. -/
theorem positivePartGrad_component_memLp
    {Ω : Set E} {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) (i : Fin d) :
    MemLp (fun x => positivePartGrad hw x i) 2 (volume.restrict Ω) := by
  let _ := (inferInstance : NeZero d)
  convert indicator_component_memLp hw.memLp.aemeasurable
    (hw.weakGrad_component_memLp i) using 1
  ext x
  by_cases hx : 0 < u x <;> simp [positivePartGrad, hx]

/-- A nonnegative smooth `H₀¹` approximation witness.  This is the exact
analytical interface consumed by the Bernstein obstacle recovery construction;
it is intentionally separated from any particular Sobolev library. -/
structure NonnegativeH01ApproximationWitness
    (u : E → ℝ) (Ω : Set E) where
  weakWitness : MemW1pWitness 2 u Ω
  approx : ℕ → E → ℝ
  smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  compactSupport : ∀ n, HasCompactSupport (approx n)
  support_subset : ∀ n, tsupport (approx n) ⊆ Ω
  nonnegative : ∀ n x, 0 ≤ approx n x
  function_tendsto :
    Tendsto (fun n => eLpNorm (fun x => approx n x - u x) 2
      (volume.restrict Ω)) atTop (nhds 0)
  gradient_tendsto : ∀ i : Fin d,
    Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ (approx n) x) (EuclideanSpace.single i 1) -
        weakWitness.weakGrad x i)
      2 (volume.restrict Ω)) atTop (nhds 0)

/-- A nonnegative approximation witness is, in particular, an `H₀¹` proof. -/
theorem NonnegativeH01ApproximationWitness.memH01
    {u : E → ℝ} {Ω : Set E}
    (D : NonnegativeH01ApproximationWitness u Ω) :
    MemH01 u Ω := by
  refine ⟨D.weakWitness.memW1p, ?_⟩
  exact ⟨D.weakWitness, D.approx, D.smooth, D.compactSupport,
    D.support_subset, D.function_tendsto, D.gradient_tendsto⟩

end SobolevH01Port
end BernsteinObstacle
