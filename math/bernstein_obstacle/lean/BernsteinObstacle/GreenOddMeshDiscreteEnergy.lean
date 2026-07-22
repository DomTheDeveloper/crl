import BernsteinObstacle.GreenOddMeshFiniteSums
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Actual odd-mesh P1 Green energy

This file connects the finite nodal sums to the removable-singularity closed
expression.  Consequently the norm limit in `GreenOddMeshClosedLimit` is the
limit of the genuine continuous piecewise-linear interpolant energy.
-/

/-- Width of the uniform mesh with `2m+1` cells. -/
def oddUniformMeshWidth (m : ℕ) : ℝ :=
  2 / (2 * (m : ℝ) + 1)

/-- Every odd uniform mesh width is positive. -/
theorem oddUniformMeshWidth_pos (m : ℕ) : 0 < oddUniformMeshWidth m := by
  unfold oddUniformMeshWidth
  positivity

/-- The odd mesh width is nonzero. -/
theorem oddUniformMeshWidth_ne_zero (m : ℕ) : oddUniformMeshWidth m ≠ 0 :=
  (oddUniformMeshWidth_pos m).ne'

/-- The hyperbolic denominator is nonzero on an odd mesh. -/
theorem sinh_oddUniformMeshWidth_ne_zero (m : ℕ) :
    Real.sinh (oddUniformMeshWidth m) ≠ 0 := by
  exact ne_of_gt (Real.sinh_pos_iff.mpr (oddUniformMeshWidth_pos m))

/-- Location of the last positive-half node for a mesh with `2m+1` cells. -/
theorem oddUniformMesh_contact_relation (m : ℕ) :
    (m : ℝ) * oddUniformMeshWidth m =
      1 - oddUniformMeshWidth m / 2 := by
  unfold oddUniformMeshWidth
  have hden : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The total odd-mesh length is two. -/
theorem oddUniformMesh_total_relation (m : ℕ) :
    (2 * (m : ℝ) + 1) * oddUniformMeshWidth m = 2 := by
  unfold oddUniformMeshWidth
  have hden : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]

/-- Genuine finite derivative-energy sum before normalization by `sinh(1)^2`. -/
def oddGreenDerivativeFiniteSum (m : ℕ) (h : ℝ) : ℝ :=
  ∑ r ∈ Finset.range m,
    (oddGreenSinhNode h (r + 1) - oddGreenSinhNode h r) ^ 2

/-- Genuine finite value-energy sum before normalization by `sinh(1)^2`. -/
def oddGreenValueFiniteSum (m : ℕ) (h : ℝ) : ℝ :=
  ∑ r ∈ Finset.range m,
    (oddGreenSinhNode h (r + 1) ^ 2 +
      oddGreenSinhNode h (r + 1) * oddGreenSinhNode h r +
      oddGreenSinhNode h r ^ 2)

/-- Exact squared `H¹` energy of the odd-mesh nodal P1 interpolant.

The central segment is constant, hence contributes only
`h * sinh(mh)^2 / sinh(1)^2`.  Every other cell occurs twice by symmetry. -/
def oddGreenP1Energy (m : ℕ) (h : ℝ) : ℝ :=
  (h * oddGreenSinhNode h m ^ 2 +
      (2 / h) * oddGreenDerivativeFiniteSum m h +
      (2 * h / 3) * oddGreenValueFiniteSum m h) /
    (Real.sinh 1) ^ 2

/-- Primitive closed form obtained by replacing the three finite sums by the
certified square and adjacent-product closed formulas. -/
def oddGreenP1EnergyPrimitiveClosed (m : ℕ) (h : ℝ) : ℝ :=
  (h * oddGreenSinhNode h m ^ 2 +
      (2 / h) *
        (oddGreenSinhSquareClosed m h +
          oddGreenSinhSquareClosed (m - 1) h -
          2 * oddGreenSinhProductClosed m h) +
      (2 * h / 3) *
        (oddGreenSinhSquareClosed m h +
          oddGreenSinhSquareClosed (m - 1) h +
          oddGreenSinhProductClosed m h)) /
    (Real.sinh 1) ^ 2

/-- The finite value sum is the sum of the two square sums and the adjacent
product sum. -/
theorem oddGreenValueFiniteSum_eq
    (m : ℕ) (h : ℝ) :
    oddGreenValueFiniteSum m h =
      oddGreenSinhSquareSum m h + oddGreenSinhSquareSum (m - 1) h +
        oddGreenSinhProductSum m h := by
  unfold oddGreenValueFiniteSum oddGreenSinhSquareSum oddGreenSinhProductSum
  calc
    (∑ r ∈ Finset.range m,
      (oddGreenSinhNode h (r + 1) ^ 2 +
        oddGreenSinhNode h (r + 1) * oddGreenSinhNode h r +
        oddGreenSinhNode h r ^ 2)) =
      (∑ r ∈ Finset.range m, oddGreenSinhNode h (r + 1) ^ 2) +
        (∑ r ∈ Finset.range m,
          oddGreenSinhNode h (r + 1) * oddGreenSinhNode h r) +
        (∑ r ∈ Finset.range m, oddGreenSinhNode h r ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ r ∈ Finset.range m, oddGreenSinhNode h (r + 1) ^ 2) +
        (∑ r ∈ Finset.range m,
          oddGreenSinhNode h (r + 1) * oddGreenSinhNode h r) +
        oddGreenSinhSquareSum (m - 1) h := by
      rw [oddGreenZeroStartSquareSum_eq]
    _ = (∑ r ∈ Finset.range m, oddGreenSinhNode h (r + 1) ^ 2) +
        oddGreenSinhSquareSum (m - 1) h +
        (∑ r ∈ Finset.range m,
          oddGreenSinhNode h (r + 1) * oddGreenSinhNode h r) := by ring

/-- The actual finite P1 energy equals the primitive closed form. -/
theorem oddGreenP1Energy_eq_primitiveClosed
    (m : ℕ) (h : ℝ) (hh : Real.sinh h ≠ 0) :
    oddGreenP1Energy m h = oddGreenP1EnergyPrimitiveClosed m h := by
  unfold oddGreenP1Energy oddGreenP1EnergyPrimitiveClosed
  unfold oddGreenDerivativeFiniteSum
  rw [oddGreenSinhDifferenceSum_eq,
    oddGreenValueFiniteSum_eq,
    oddGreenSinhSquareSum_eq_closed m h hh,
    oddGreenSinhSquareSum_eq_closed (m - 1) h hh,
    oddGreenSinhProductSum_eq_closed m h hh]

/-- Product-to-sum identity for hyperbolic sine and cosine. -/
theorem two_sinh_mul_cosh (a b : ℝ) :
    2 * Real.sinh a * Real.cosh b =
      Real.sinh (a + b) + Real.sinh (a - b) := by
  rw [Real.sinh_add, Real.sinh_sub]
  ring

/-- Symmetric second-difference identity for `sinh`. -/
theorem sinh_symmetric_second_difference (a h : ℝ) :
    Real.sinh (a + h) + Real.sinh (a - h) - 2 * Real.sinh a =
      4 * Real.sinh a * Real.sinh (h / 2) ^ 2 := by
  rw [Real.sinh_add, Real.sinh_sub]
  have hcosh : Real.cosh h - 1 = 2 * Real.sinh (h / 2) ^ 2 := by
    rw [show h = 2 * (h / 2) by ring, Real.cosh_two_mul,
      Real.cosh_sq]
    ring
  nlinarith

/-- Specialized closed square sum at the last positive-half node. -/
theorem oddGreenSinhSquareClosed_contact
    (m : ℕ) (h : ℝ)
    (hh : Real.sinh h ≠ 0)
    (htotal : (2 * (m : ℝ) + 1) * h = 2) :
    oddGreenSinhSquareClosed m h =
      (Real.sinh 2 - Real.sinh h) / (4 * Real.sinh h) - (m : ℝ) / 2 := by
  have hsum : (m : ℝ) * h + (((m : ℝ) + 1) * h) = 2 := by
    nlinarith
  have hdiff : (m : ℝ) * h - (((m : ℝ) + 1) * h) = -h := by ring
  have hprod := two_sinh_mul_cosh ((m : ℝ) * h) (((m : ℝ) + 1) * h)
  rw [hsum, hdiff, Real.sinh_neg] at hprod
  unfold oddGreenSinhSquareClosed
  field_simp [hh] at hprod ⊢
  nlinarith

/-- Specialized closed square sum one node before contact. -/
theorem oddGreenSinhSquareClosed_beforeContact
    (n : ℕ) (h : ℝ)
    (hh : Real.sinh h ≠ 0)
    (htotal : (2 * (((n + 1 : ℕ) : ℝ)) + 1) * h = 2) :
    oddGreenSinhSquareClosed n h =
      (Real.sinh (2 - 2 * h) - Real.sinh h) /
          (4 * Real.sinh h) - (n : ℝ) / 2 := by
  have hsum : (n : ℝ) * h + (((n : ℝ) + 1) * h) = 2 - 2 * h := by
    push_cast at htotal
    nlinarith
  have hdiff : (n : ℝ) * h - (((n : ℝ) + 1) * h) = -h := by ring
  have hprod := two_sinh_mul_cosh ((n : ℝ) * h) (((n : ℝ) + 1) * h)
  rw [hsum, hdiff, Real.sinh_neg] at hprod
  unfold oddGreenSinhSquareClosed
  field_simp [hh] at hprod ⊢
  nlinarith

/-- Specialized adjacent-product sum on an odd mesh. -/
theorem oddGreenSinhProductClosed_contact
    (m : ℕ) (h : ℝ)
    (hcontact : (m : ℝ) * h = 1 - h / 2) :
    oddGreenSinhProductClosed m h =
      Real.sinh (2 - h) / (4 * Real.sinh h) -
        (m : ℝ) * Real.cosh h / 2 := by
  unfold oddGreenSinhProductClosed
  have harg : 2 * (m : ℝ) * h = 2 - h := by nlinarith
  rw [harg]

/-- Exact identification of the actual odd-mesh P1 energy with the closed
removable-singularity expression. -/
theorem oddGreenP1Energy_eq_closed
    (n : ℕ) :
    oddGreenP1Energy (n + 1) (oddUniformMeshWidth (n + 1)) =
      oddGreenInterpolantEnergyClosed (oddUniformMeshWidth (n + 1)) := by
  let h := oddUniformMeshWidth (n + 1)
  have hh0 : 0 < h := oddUniformMeshWidth_pos (n + 1)
  have hh : h ≠ 0 := hh0.ne'
  have hsinh : Real.sinh h ≠ 0 :=
    sinh_oddUniformMeshWidth_ne_zero (n + 1)
  have hcontact : (((n + 1 : ℕ) : ℝ)) * h = 1 - h / 2 :=
    oddUniformMesh_contact_relation (n + 1)
  have htotal : (2 * (((n + 1 : ℕ) : ℝ)) + 1) * h = 2 :=
    oddUniformMesh_total_relation (n + 1)
  rw [oddGreenP1Energy_eq_primitiveClosed (n + 1) h hsinh]
  rw [oddGreenSinhSquareClosed_contact (n + 1) h hsinh htotal,
    oddGreenSinhSquareClosed_beforeContact n h hsinh htotal,
    oddGreenSinhProductClosed_contact (n + 1) h hcontact]
  have hsh : Real.sinh (1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr zero_lt_one)
  have hh2 : h / 2 ≠ 0 := div_ne_zero hh (by norm_num)
  have hsinhc_h := sinhc_eq_sinh_div h hh
  have hsinhc_h2 := sinhc_eq_sinh_div (h / 2) hh2
  have hsym := sinh_symmetric_second_difference (2 - h) h
  have hcosh : Real.cosh h - 1 = 2 * Real.sinh (h / 2) ^ 2 := by
    rw [show h = 2 * (h / 2) by ring, Real.cosh_two_mul,
      Real.cosh_sq]
    ring
  unfold oddGreenP1EnergyPrimitiveClosed oddGreenSinhNode
  unfold oddGreenInterpolantEnergyClosed oddGreenCentralEnergyClosed
    oddGreenDerivativeEnergyClosed oddGreenValueEnergyClosed
  rw [hsinhc_h, hsinhc_h2]
  have hnode : ((n + 1 : ℕ) : ℝ) * h = 1 - h / 2 := hcontact
  rw [hnode]
  field_simp [hh, hsinh, hsh] at hsym ⊢
  nlinarith

/-- The genuine odd-mesh P1 squared energy converges to `2/tanh(1)`. -/
theorem oddGreenP1Energy_tendsto :
    Tendsto
      (fun n => oddGreenP1Energy (n + 1) (oddUniformMeshWidth (n + 1)))
      atTop (𝓝 (2 / Real.tanh 1)) := by
  have hh : Tendsto (fun n => oddUniformMeshWidth (n + 1)) atTop (𝓝 0) := by
    unfold oddUniformMeshWidth
    norm_num
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hclosed := oddGreenInterpolantEnergyClosed_tendsto
    (fun n => oddUniformMeshWidth (n + 1)) hh
  apply tendsto_congr' _ |>.mpr hclosed
  exact Eventually.of_forall fun n => oddGreenP1Energy_eq_closed n

/-- Genuine odd-mesh P1 norm. -/
def oddGreenP1Norm (m : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt (oddGreenP1Energy m h)

/-- The genuine odd-mesh P1 norm converges to the exact Green trace norm. -/
theorem oddGreenP1Norm_tendsto :
    Tendsto
      (fun n => oddGreenP1Norm (n + 1) (oddUniformMeshWidth (n + 1)))
      atTop (𝓝 greenTraceProfileNorm) := by
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp
    oddGreenP1Energy_tendsto
  simpa [oddGreenP1Norm, greenTraceProfileNorm] using ht

end

end BernsteinObstacle
