import BernsteinObstacle.PhysicalOddMeshQuadratic
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# A complete one-step fitted AFEM for the quadratic benchmark

The model problem is `u(x)=x^2` on an odd uniform mesh.  Its unique central
cell is `[-h/2,h/2]`.  The adaptive geometry step inserts the detected contact
point `0`, replacing that cell by `[-h/2,0]` and `[0,h/2]`.

After this single step, the target has exact nonnegative degree-`p` Bernstein
coefficients on both children for every `p ≥ 2`.  Thus the coefficient-cone
best-approximation error of this benchmark becomes exactly zero.
-/

/-- Degree-`p` coefficients of `(1-t)^2`. -/
def oneMinusQuadraticCoeff (p k : ℕ) : ℝ :=
  1 - 2 * ((k : ℝ) / (p : ℝ)) + quadraticMonomialCoeff p k

/-- Exact Bernstein representation of the reflected quadratic `(1-t)^2`. -/
theorem oneMinusQuadraticCoeff_curve_eq
    (p : ℕ) (hp : 2 ≤ p) (t : ℝ) :
    curve p (oneMinusQuadraticCoeff p) t = (1 - t) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have h0 := basis_sum_eq_one p t
  have h1 := basis_firstMoment p t
  have h2 :
      (∑ k ∈ Finset.range (p + 1),
        quadraticMonomialCoeff p k * basis p k t) = t ^ 2 := by
    simpa [curve] using quadraticMonomial_eq_bernsteinCurve p hp t
  unfold curve oneMinusQuadraticCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        (1 - 2 * ((k : ℝ) / (p : ℝ)) + quadraticMonomialCoeff p k) *
          basis p k t) =
        (∑ k ∈ Finset.range (p + 1), basis p k t) -
          (2 / (p : ℝ)) *
            (∑ k ∈ Finset.range (p + 1), (k : ℝ) * basis p k t) +
          (∑ k ∈ Finset.range (p + 1),
            quadraticMonomialCoeff p k * basis p k t) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 1 - (2 / (p : ℝ)) * ((p : ℝ) * t) + t ^ 2 := by
      rw [h0, h1, h2]
    _ = (1 - t) ^ 2 := by field_simp [hp0]; ring

/-- The coefficients of `(1-t)^2` are nonnegative. -/
theorem oneMinusQuadraticCoeff_nonneg
    (p k : ℕ) (hp : 2 ≤ p) (hk : k ∈ Finset.range (p + 1)) :
    0 ≤ oneMinusQuadraticCoeff p k := by
  have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hDpos := quadraticMomentDenominator_pos p hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  have hid :
      oneMinusQuadraticCoeff p k =
        (((p : ℝ) - (k : ℝ)) * (((p : ℝ) - (k : ℝ)) - 1)) /
          quadraticMomentDenominator p := by
    unfold oneMinusQuadraticCoeff quadraticMonomialCoeff
    unfold quadraticMomentDenominator
    rw [natCast_mul_pred p, natCast_mul_pred k]
    field_simp [hp0, hp1]
    ring
  rw [hid]
  apply div_nonneg
  · by_cases hEq : k = p
    · subst k
      norm_num
    · have hklt : k < p := lt_of_le_of_ne hkp hEq
      have hsucc : k + 1 ≤ p := Nat.succ_le_iff.mpr hklt
      have hreal : (k : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hsucc
      nlinarith
  · exact hDpos.le

/-- Coefficients on the fitted right child `[0,h/2]`. -/
def rightFittedQuadraticCoeff (p k : ℕ) (h : ℝ) : ℝ :=
  (h / 2) ^ 2 * quadraticMonomialCoeff p k

/-- Coefficients on the fitted left child `[-h/2,0]`. -/
def leftFittedQuadraticCoeff (p k : ℕ) (h : ℝ) : ℝ :=
  (h / 2) ^ 2 * oneMinusQuadraticCoeff p k

/-- The right fitted child represents the physical target exactly. -/
theorem rightFittedQuadratic_exact
    (p : ℕ) (hp : 2 ≤ p) (h t : ℝ) :
    curve p (fun k => rightFittedQuadraticCoeff p k h) t =
      ((h / 2) * t) ^ 2 := by
  unfold curve rightFittedQuadraticCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        ((h / 2) ^ 2 * quadraticMonomialCoeff p k) * basis p k t) =
        (h / 2) ^ 2 *
          (∑ k ∈ Finset.range (p + 1),
            quadraticMonomialCoeff p k * basis p k t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (h / 2) ^ 2 * t ^ 2 := by
      have hquad := quadraticMonomial_eq_bernsteinCurve p hp t
      simpa [curve] using congrArg (fun z => (h / 2) ^ 2 * z) hquad
    _ = ((h / 2) * t) ^ 2 := by ring

/-- The left fitted child represents the physical target exactly. -/
theorem leftFittedQuadratic_exact
    (p : ℕ) (hp : 2 ≤ p) (h t : ℝ) :
    curve p (fun k => leftFittedQuadraticCoeff p k h) t =
      (-h / 2 + (h / 2) * t) ^ 2 := by
  unfold curve leftFittedQuadraticCoeff
  calc
    (∑ k ∈ Finset.range (p + 1),
        ((h / 2) ^ 2 * oneMinusQuadraticCoeff p k) * basis p k t) =
        (h / 2) ^ 2 *
          curve p (oneMinusQuadraticCoeff p) t := by
      unfold curve
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (h / 2) ^ 2 * (1 - t) ^ 2 := by
      rw [oneMinusQuadraticCoeff_curve_eq p hp t]
    _ = (-h / 2 + (h / 2) * t) ^ 2 := by ring

/-- Every fitted right-child coefficient is nonnegative. -/
theorem rightFittedQuadraticCoeff_nonneg
    (p k : ℕ) (h : ℝ) (hp : 2 ≤ p) :
    0 ≤ rightFittedQuadraticCoeff p k h := by
  unfold rightFittedQuadraticCoeff
  exact mul_nonneg (sq_nonneg _) (quadraticMonomialCoeff_nonneg p k hp)

/-- Every fitted left-child coefficient is nonnegative. -/
theorem leftFittedQuadraticCoeff_nonneg
    (p k : ℕ) (h : ℝ) (hp : 2 ≤ p)
    (hk : k ∈ Finset.range (p + 1)) :
    0 ≤ leftFittedQuadraticCoeff p k h := by
  unfold leftFittedQuadraticCoeff
  exact mul_nonneg (sq_nonneg _) (oneMinusQuadraticCoeff_nonneg p k hp hk)

/-- Splitting the central cell at the contact point creates two equal children. -/
theorem fittedCentralChild_widths (h : ℝ) :
    0 - (-h / 2) = h / 2 ∧ h / 2 - 0 = h / 2 := by
  constructor <;> ring

/-- The neighboring-size ratio introduced by the one-step fit is exactly two
relative to an unsplit cell of width `h`. -/
theorem fittedCentral_neighbor_ratio (h : ℝ) (hh : h ≠ 0) :
    h / (h / 2) = 2 := by
  field_simp [hh]

/-- Terminal theorem for the specified adaptive algorithm.

One geometric refinement step inserts the exact contact point.  Both child
representations are exact, all their Bernstein coefficients are nonnegative,
and the local neighboring-size ratio is two. -/
theorem oneStepFittedAFEM_exact_feasible_and_shapeRegular
    (p : ℕ) (hp : 2 ≤ p) (h : ℝ) (hh : h ≠ 0) :
    (∀ k ∈ Finset.range (p + 1),
      0 ≤ leftFittedQuadraticCoeff p k h) ∧
    (∀ k ∈ Finset.range (p + 1),
      0 ≤ rightFittedQuadraticCoeff p k h) ∧
    (∀ t, curve p (fun k => leftFittedQuadraticCoeff p k h) t =
      (-h / 2 + (h / 2) * t) ^ 2) ∧
    (∀ t, curve p (fun k => rightFittedQuadraticCoeff p k h) t =
      ((h / 2) * t) ^ 2) ∧
    h / (h / 2) = 2 := by
  constructor
  · intro k hk
    exact leftFittedQuadraticCoeff_nonneg p k h hp hk
  constructor
  · intro k hk
    exact rightFittedQuadraticCoeff_nonneg p k h hp
  constructor
  · intro t
    exact leftFittedQuadratic_exact p hp h t
  constructor
  · intro t
    exact rightFittedQuadratic_exact p hp h t
  · exact fittedCentral_neighbor_ratio h hh

end

end BernsteinObstacle
