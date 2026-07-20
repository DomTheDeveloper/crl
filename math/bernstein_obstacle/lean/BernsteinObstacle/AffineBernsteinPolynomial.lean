import BernsteinObstacle.Simplex
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Simplicial Bernstein basis as affine multivariate polynomials

The final barycentric coordinate is eliminated using
`λ_d = 1 - ∑_{i<d} λ_i`.  This realizes every simplicial Bernstein basis
function as an actual member of the total-degree polynomial space `P_n` in
`d` independent variables.
-/

/-- The `d + 1` barycentric coordinate polynomials in the standard affine
chart with the final coordinate eliminated. -/
def affineBarycentric (d : ℕ) :
    Fin (d + 1) → MvPolynomial (Fin d) ℝ :=
  Fin.snoc (fun i => MvPolynomial.X i)
    (MvPolynomial.C 1 - ∑ i : Fin d, MvPolynomial.X i)

/-- Evaluation of the affine barycentric coordinate polynomials. -/
theorem eval_affineBarycentric (d : ℕ) (x : Fin d → ℝ)
    (i : Fin (d + 1)) :
    MvPolynomial.eval x (affineBarycentric d i) =
      ((Fin.snoc x (1 - ∑ j : Fin d, x j) : Fin (d + 1) → ℝ) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [affineBarycentric]
  · simp [affineBarycentric]

/-- Every affine barycentric coordinate polynomial has total degree at most
one. -/
theorem totalDegree_affineBarycentric_le (d : ℕ) (i : Fin (d + 1)) :
    (affineBarycentric d i).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hsum :
        (∑ j : Fin d, (MvPolynomial.X j : MvPolynomial (Fin d) ℝ)).totalDegree ≤ 1 := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro j hj
      simp
    simp only [affineBarycentric, Fin.snoc_last]
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ hsum)
    simp
  · simp [affineBarycentric]

/-- The real multinomial coefficient occurring in the degree-`n` simplicial
Bernstein basis. -/
def affineBernsteinCoefficient (d n : ℕ) (α : MultiIndex d n) : ℝ :=
  (Nat.factorial n : ℝ) /
    ∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ)

/-- The simplicial Bernstein basis polynomial in `d` independent affine
coordinates. -/
def affineBernsteinPolynomial (d n : ℕ) (α : MultiIndex d n) :
    MvPolynomial (Fin d) ℝ :=
  MvPolynomial.C (affineBernsteinCoefficient d n α) *
    ∏ i : Fin (d + 1),
      (affineBarycentric d i) ^ (α.1 i : ℕ)

/-- Every affine simplicial Bernstein polynomial has total degree at most its
nominal degree `n`. -/
theorem totalDegree_affineBernsteinPolynomial_le (d n : ℕ)
    (α : MultiIndex d n) :
    (affineBernsteinPolynomial d n α).totalDegree ≤ n := by
  unfold affineBernsteinPolynomial
  calc
    (MvPolynomial.C (affineBernsteinCoefficient d n α) *
        ∏ i : Fin (d + 1),
          (affineBarycentric d i) ^ (α.1 i : ℕ)).totalDegree
        ≤ (MvPolynomial.C (affineBernsteinCoefficient d n α) :
            MvPolynomial (Fin d) ℝ).totalDegree +
          (∏ i : Fin (d + 1),
            (affineBarycentric d i) ^ (α.1 i : ℕ)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + ∑ i : Fin (d + 1),
          ((affineBarycentric d i) ^ (α.1 i : ℕ)).totalDegree := by
      apply Nat.add_le_add
      · simp
      · simpa using MvPolynomial.totalDegree_finsetProd
          (Finset.univ : Finset (Fin (d + 1)))
          (fun i => (affineBarycentric d i) ^ (α.1 i : ℕ))
    _ ≤ 0 + ∑ i : Fin (d + 1), (α.1 i : ℕ) := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro i hi
      calc
        ((affineBarycentric d i) ^ (α.1 i : ℕ)).totalDegree
            ≤ (α.1 i : ℕ) * (affineBarycentric d i).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ (α.1 i : ℕ) * 1 :=
          Nat.mul_le_mul_left _ (totalDegree_affineBarycentric_le d i)
        _ = (α.1 i : ℕ) := Nat.mul_one _
    _ = n := by simpa using α.2

/-- Each affine simplicial Bernstein polynomial belongs to `P_n`. -/
theorem affineBernsteinPolynomial_mem_restrictTotalDegree (d n : ℕ)
    (α : MultiIndex d n) :
    affineBernsteinPolynomial d n α ∈
      MvPolynomial.restrictTotalDegree (Fin d) ℝ n := by
  rw [MvPolynomial.mem_restrictTotalDegree]
  exact totalDegree_affineBernsteinPolynomial_le d n α

/-- The affine simplicial Bernstein polynomial, packaged as a vector in
`P_n`. -/
def affineBernsteinVector (d n : ℕ) (α : MultiIndex d n) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ n :=
  ⟨affineBernsteinPolynomial d n α,
    affineBernsteinPolynomial_mem_restrictTotalDegree d n α⟩

/-- Exact evaluation formula in independent affine coordinates. -/
theorem eval_affineBernsteinPolynomial (d n : ℕ)
    (α : MultiIndex d n) (x : Fin d → ℝ) :
    MvPolynomial.eval x (affineBernsteinPolynomial d n α) =
      affineBernsteinCoefficient d n α *
        ∏ i : Fin (d + 1),
          (((Fin.snoc x (1 - ∑ j : Fin d, x j) : Fin (d + 1) → ℝ) i) ^
            (α.1 i : ℕ)) := by
  unfold affineBernsteinPolynomial
  rw [map_mul, MvPolynomial.eval_C, map_prod]
  refine congrArg (fun z : ℝ => affineBernsteinCoefficient d n α * z) ?_
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow, eval_affineBarycentric]

/-- Convert affine coordinates satisfying the standard-simplex inequalities
into a barycentric point. -/
def affinePointToBarycentric (d : ℕ) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i : Fin d, x i ≤ 1) :
    BarycentricPoint d := by
  refine ⟨Fin.snoc x (1 - ∑ i : Fin d, x i), ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
      linarith
    · simpa using hx j
  · rw [Fin.sum_univ_castSucc]
    simp

/-- Evaluation of the affine polynomial is exactly the original simplicial
Bernstein basis weight on the corresponding standard-simplex point. -/
theorem eval_affineBernsteinPolynomial_eq_simplexBasis (d n : ℕ)
    (α : MultiIndex d n) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i : Fin d, x i ≤ 1) :
    MvPolynomial.eval x (affineBernsteinPolynomial d n α) =
      simplexBasis d n α (affinePointToBarycentric d x hx hsum) := by
  rw [eval_affineBernsteinPolynomial]
  rfl

end

end BernsteinObstacle
