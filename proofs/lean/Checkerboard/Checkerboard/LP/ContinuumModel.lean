import Mathlib

/-!
# Continuum primal and dual for the four-direction checkerboard LP

The primal constraints are stated in their test-function form. For nonnegative
measurable test functions this is equivalent to domination of the two paired
pushforward measures by four times Lebesgue measure on `[0,1]`.

Using `ℝ≥0∞`-valued functions makes weak duality independent of integrability
side conditions: all integrands are nonnegative and the Lebesgue integral is the
extended nonnegative integral.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

/-- Ambient continuum plane. -/
abbrev ContinuumPoint := ℝ × ℝ

/-- Fundamental triangular chamber for the symmetry-reduced LP. -/
def continuumTriangle : Set ContinuumPoint :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 + z.2 ≤ 1}

lemma measurableSet_continuumTriangle : MeasurableSet continuumTriangle := by
  unfold continuumTriangle
  exact (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_fst).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))

/-- The four affine coordinates corresponding to rows/columns and diagonals. -/
def coordX (z : ContinuumPoint) : ℝ := z.1

def coordOneSubY (z : ContinuumPoint) : ℝ := 1 - z.2

def coordSum (z : ContinuumPoint) : ℝ := z.1 + z.2

def coordDiff (z : ContinuumPoint) : ℝ := z.1 - z.2

lemma measurable_coordX : Measurable coordX := measurable_fst
lemma measurable_coordOneSubY : Measurable coordOneSubY := measurable_const.sub measurable_snd
lemma measurable_coordSum : Measurable coordSum := measurable_fst.add measurable_snd
lemma measurable_coordDiff : Measurable coordDiff := measurable_fst.sub measurable_snd

/-- Lebesgue measure restricted to the unit interval. -/
def unitIntervalVolume : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The obstacle integrand associated to a pair of nonnegative dual functions. -/
def pairedObstacle (A B : ℝ → ℝ≥0∞) (z : ContinuumPoint) : ℝ≥0∞ :=
  A (coordX z) + A (coordOneSubY z) + B (coordSum z) + B (coordDiff z)

lemma measurable_pairedObstacle {A B : ℝ → ℝ≥0∞}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (pairedObstacle A B) := by
  unfold pairedObstacle
  exact (((hA.comp measurable_coordX).add (hA.comp measurable_coordOneSubY)).add
    (hB.comp measurable_coordSum)).add (hB.comp measurable_coordDiff)

/-- Feasibility for the continuum primal.

`projection_bound` is the test-function form of the two paired projection
constraints. It is deliberately quantified only over measurable nonnegative
functions, because the codomain `ℝ≥0∞` already encodes nonnegativity.
-/
structure ContinuumPrimalFeasible (μ : Measure ContinuumPoint) : Prop where
  support : ∀ᵐ z ∂μ, z ∈ continuumTriangle
  projection_bound :
    ∀ (A B : ℝ → ℝ≥0∞), Measurable A → Measurable B →
      (∫⁻ z, pairedObstacle A B z ∂μ) ≤
        4 * ((∫⁻ t, A t ∂unitIntervalVolume) + (∫⁻ t, B t ∂unitIntervalVolume))

/-- Feasibility for the continuum dual obstacle problem. -/
structure ContinuumDualFeasible (A B : ℝ → ℝ≥0∞) : Prop where
  measurable_A : Measurable A
  measurable_B : Measurable B
  obstacle : ∀ z ∈ continuumTriangle, 1 ≤ pairedObstacle A B z

/-- Total mass of a continuum primal candidate. -/
def continuumPrimalValue (μ : Measure ContinuumPoint) : ℝ≥0∞ := μ Set.univ

/-- Objective value of a continuum dual candidate. -/
def continuumDualValue (A B : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  4 * ((∫⁻ t, A t ∂unitIntervalVolume) + (∫⁻ t, B t ∂unitIntervalVolume))

/-- Weak duality for the exact continuum primal and dual. -/
theorem continuum_weak_duality
    {μ : Measure ContinuumPoint} {A B : ℝ → ℝ≥0∞}
    (hμ : ContinuumPrimalFeasible μ) (hAB : ContinuumDualFeasible A B) :
    continuumPrimalValue μ ≤ continuumDualValue A B := by
  calc
    continuumPrimalValue μ = ∫⁻ _z, (1 : ℝ≥0∞) ∂μ := by
      simp [continuumPrimalValue]
    _ ≤ ∫⁻ z, pairedObstacle A B z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hμ.support] with z hz
      exact hAB.obstacle z hz
    _ ≤ 4 * ((∫⁻ t, A t ∂unitIntervalVolume) +
        (∫⁻ t, B t ∂unitIntervalVolume)) :=
      hμ.projection_bound A B hAB.measurable_A hAB.measurable_B
    _ = continuumDualValue A B := rfl

/-- A matched primal/dual pair certifies the common continuum optimum without
any appeal to numerical optimization. -/
theorem continuum_optimality_of_matched_certificates
    {μ : Measure ContinuumPoint} {A B : ℝ → ℝ≥0∞} {v : ℝ≥0∞}
    (hμ : ContinuumPrimalFeasible μ) (hAB : ContinuumDualFeasible A B)
    (hprimal : continuumPrimalValue μ = v)
    (hdual : continuumDualValue A B = v) :
    continuumPrimalValue μ = continuumDualValue A B := by
  calc
    continuumPrimalValue μ = v := hprimal
    _ = continuumDualValue A B := hdual.symm

end

end Checkerboard
