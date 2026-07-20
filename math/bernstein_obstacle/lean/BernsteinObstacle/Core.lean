import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

open scoped BigOperators Polynomial

namespace BernsteinObstacle

/-- The one-dimensional degree-`n`, index-`k` Bernstein basis function. -/
def basis (n k : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)

@[simp]
theorem basis_eq_eval (n k : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℝ n k).eval x = basis n k x := by
  simp [basis, bernsteinPolynomial, mul_assoc]

/-- Bernstein basis functions are nonnegative on the unit interval. -/
theorem basis_nonneg (n k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ basis n k x := by
  unfold basis
  have hchoose : 0 ≤ (Nat.choose n k : ℝ) := by positivity
  have hxpow : 0 ≤ x ^ k := pow_nonneg hx0 k
  have hsubpow : 0 ≤ (1 - x) ^ (n - k) :=
    pow_nonneg (sub_nonneg.mpr hx1) (n - k)
  exact mul_nonneg (mul_nonneg hchoose hxpow) hsubpow

/-- The Bernstein basis is a partition of unity. -/
theorem basis_sum_eq_one (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1), basis n k x) = 1 := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (bernsteinPolynomial.sum ℝ n)
  simpa [basis, bernsteinPolynomial, mul_assoc] using h

/-- A polynomial curve written in the degree-`n` Bernstein basis. -/
def curve (n : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), c k * basis n k x

/-- Abstract finite-certificate principle used by the Bernstein bridge. -/
theorem finite_nonnegative_certificate {ι : Type*} [Fintype ι]
    (coeff weight : ι → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ ∑ i, coeff i * weight i := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hcoeff i) (hweight i)

/-- Nonnegative Bernstein coefficients certify pointwise nonnegativity. -/
theorem curve_nonneg (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ k ∈ Finset.range (n + 1), 0 ≤ c k)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ curve n c x := by
  unfold curve
  exact Finset.sum_nonneg fun k hk =>
    mul_nonneg (hc k hk) (basis_nonneg n k hx0 hx1)

/-- Bernstein curves are monotone with respect to their coefficients. -/
theorem curve_mono (n : ℕ) (c d : ℕ → ℝ)
    (hcd : ∀ k ∈ Finset.range (n + 1), c k ≤ d k)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    curve n c x ≤ curve n d x := by
  unfold curve
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (hcd k hk) (basis_nonneg n k hx0 hx1)

/-- Lower coefficient bounds imply the same pointwise lower bound. -/
theorem curve_lower_bound (n : ℕ) (c : ℕ → ℝ) (m : ℝ)
    (hc : ∀ k ∈ Finset.range (n + 1), m ≤ c k)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    m ≤ curve n c x := by
  have hsum :
      (∑ k ∈ Finset.range (n + 1), m * basis n k x) ≤
        ∑ k ∈ Finset.range (n + 1), c k * basis n k x := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hc k hk) (basis_nonneg n k hx0 hx1)
  calc
    m = m * 1 := by ring
    _ = m * (∑ k ∈ Finset.range (n + 1), basis n k x) := by
      rw [basis_sum_eq_one]
    _ = ∑ k ∈ Finset.range (n + 1), m * basis n k x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (n + 1), c k * basis n k x := hsum
    _ = curve n c x := rfl

/-- Upper coefficient bounds imply the same pointwise upper bound. -/
theorem curve_upper_bound (n : ℕ) (c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ k ∈ Finset.range (n + 1), c k ≤ M)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    curve n c x ≤ M := by
  have hsum :
      (∑ k ∈ Finset.range (n + 1), c k * basis n k x) ≤
        ∑ k ∈ Finset.range (n + 1), M * basis n k x := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hc k hk) (basis_nonneg n k hx0 hx1)
  calc
    curve n c x = ∑ k ∈ Finset.range (n + 1), c k * basis n k x := rfl
    _ ≤ ∑ k ∈ Finset.range (n + 1), M * basis n k x := hsum
    _ = M * (∑ k ∈ Finset.range (n + 1), basis n k x) := by
      rw [Finset.mul_sum]
    _ = M := by rw [basis_sum_eq_one, mul_one]

/-- The full convex-hull property of a one-dimensional Bernstein curve. -/
theorem curve_mem_Icc (n : ℕ) (c : ℕ → ℝ) (m M : ℝ)
    (hc : ∀ k ∈ Finset.range (n + 1), c k ∈ Set.Icc m M)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    curve n c x ∈ Set.Icc m M := by
  constructor
  · exact curve_lower_bound n c m (fun k hk => (hc k hk).1) hx0 hx1
  · exact curve_upper_bound n c M (fun k hk => (hc k hk).2) hx0 hx1

/-- Coefficient clipping to the nonnegative orthant. -/
def clip (a : ℝ) : ℝ := max a 0

@[simp]
theorem clip_nonneg (a : ℝ) : 0 ≤ clip a := by
  exact le_max_right a 0

theorem le_clip (a : ℝ) : a ≤ clip a := by
  exact le_max_left a 0

/-- Clipping coefficients cannot decrease the represented Bernstein curve. -/
theorem curve_le_clipped_curve (n : ℕ) (c : ℕ → ℝ)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    curve n c x ≤ curve n (fun k => clip (c k)) x := by
  exact curve_mono n c (fun k => clip (c k))
    (fun k _ => le_clip (c k)) hx0 hx1

/-- A clipped Bernstein curve is pointwise nonnegative. -/
theorem clipped_curve_nonneg (n : ℕ) (c : ℕ → ℝ)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ curve n (fun k => clip (c k)) x := by
  exact curve_nonneg n (fun k => clip (c k))
    (fun k _ => clip_nonneg (c k)) hx0 hx1

/-- An obstacle plus a Bernstein gap. -/
def obstacleApprox (ψ : ℝ → ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ψ x + curve n c x

/-- Downstream obstacle theorem: the finite coefficient certificate guarantees no penetration. -/
theorem noPenetration_of_nonnegative_coefficients
    (ψ : ℝ → ℝ) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ k ∈ Finset.range (n + 1), 0 ≤ c k)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ψ x ≤ obstacleApprox ψ n c x := by
  unfold obstacleApprox
  have hgap : 0 ≤ curve n c x := curve_nonneg n c hc hx0 hx1
  linarith

/-- Clipping arbitrary gap coefficients yields a certified nonpenetrating approximation. -/
theorem noPenetration_after_clipping
    (ψ : ℝ → ℝ) (n : ℕ) (c : ℕ → ℝ)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ψ x ≤ obstacleApprox ψ n (fun k => clip (c k)) x := by
  exact noPenetration_of_nonnegative_coefficients ψ n (fun k => clip (c k))
    (fun k _ => clip_nonneg (c k)) hx0 hx1

end BernsteinObstacle
