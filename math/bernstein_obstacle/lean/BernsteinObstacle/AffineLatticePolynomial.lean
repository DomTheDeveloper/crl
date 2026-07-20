import BernsteinObstacle.AffineLattice
import BernsteinObstacle.LatticeCardinal
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Cardinal polynomials in independent simplex coordinates

The barycentric coordinates satisfy one affine relation.  This file eliminates
the final coordinate, realizes it as `n - sum Xᵢ` in the scaled lattice
coordinates, and constructs the cardinal polynomials in exactly `d`
independent variables.
-/

section AffineLatticePolynomial

/-- Evaluate the falling-factorial polynomial at an arbitrary multivariate
polynomial. -/
def descPochhammerAt {ι : Type*} (q : MvPolynomial ι ℝ) (a : ℕ) :
    MvPolynomial ι ℝ :=
  Polynomial.eval₂ MvPolynomial.C q (descPochhammer ℝ a)

/-- Falling factorials at a polynomial argument have their expected product
form. -/
theorem descPochhammerAt_eq_prod {ι : Type*}
    (q : MvPolynomial ι ℝ) (a : ℕ) :
    descPochhammerAt q a = ∏ m ∈ Finset.range a, (q - MvPolynomial.C (m : ℝ)) := by
  induction a with
  | zero => simp [descPochhammerAt]
  | succ a ih =>
      rw [Finset.prod_range_succ]
      unfold descPochhammerAt
      rw [descPochhammer_succ_right, Polynomial.eval₂_mul]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_natCast]
      change descPochhammerAt q a * (q - MvPolynomial.C (a : ℝ)) =
        (∏ m ∈ Finset.range a, (q - MvPolynomial.C (m : ℝ))) *
          (q - MvPolynomial.C (a : ℝ))
      rw [ih]

/-- Substituting a polynomial of total degree at most one into a falling
factorial of order `a` gives total degree at most `a`. -/
theorem totalDegree_descPochhammerAt_le {ι : Type*}
    (q : MvPolynomial ι ℝ) (a : ℕ) (hq : q.totalDegree ≤ 1) :
    (descPochhammerAt q a).totalDegree ≤ a := by
  rw [descPochhammerAt_eq_prod]
  calc
    (∏ m ∈ Finset.range a, (q - MvPolynomial.C (m : ℝ))).totalDegree
        ≤ ∑ m ∈ Finset.range a,
          (q - MvPolynomial.C (m : ℝ)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _m ∈ Finset.range a, 1 := by
      apply Finset.sum_le_sum
      intro m hm
      exact (MvPolynomial.totalDegree_sub_C_le q (m : ℝ)).trans hq
    _ = a := by simp

/-- Normalize a falling-factorial polynomial by the relevant factorial. -/
def normalizedDescPochhammerAt {ι : Type*}
    (q : MvPolynomial ι ℝ) (a : ℕ) : MvPolynomial ι ℝ :=
  MvPolynomial.C ((a.factorial : ℝ)⁻¹) * descPochhammerAt q a

/-- Normalization does not increase the degree. -/
theorem totalDegree_normalizedDescPochhammerAt_le {ι : Type*}
    (q : MvPolynomial ι ℝ) (a : ℕ) (hq : q.totalDegree ≤ 1) :
    (normalizedDescPochhammerAt q a).totalDegree ≤ a := by
  unfold normalizedDescPochhammerAt
  calc
    (MvPolynomial.C ((a.factorial : ℝ)⁻¹) * descPochhammerAt q a).totalDegree
        ≤ (MvPolynomial.C ((a.factorial : ℝ)⁻¹) : MvPolynomial ι ℝ).totalDegree +
          (descPochhammerAt q a).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + a := Nat.add_le_add (by simp) (totalDegree_descPochhammerAt_le q a hq)
    _ = a := by simp

/-- Evaluation at a natural value recovers the normalized lattice factor. -/
theorem eval_normalizedDescPochhammerAt_nat {ι : Type*}
    (q : MvPolynomial ι ℝ) (a : ℕ) (x : ι → ℝ) (b : ℕ)
    (hq : MvPolynomial.eval x q = (b : ℝ)) :
    MvPolynomial.eval x (normalizedDescPochhammerAt q a) = latticeFactor a b := by
  unfold normalizedDescPochhammerAt descPochhammerAt MvPolynomial.eval
  rw [map_mul, map_C, Polynomial.hom_eval₂]
  simp [hq, descPochhammer_eval_eq_descFactorial, latticeFactor,
    div_eq_mul_inv, mul_comm]

/-- The scaled barycentric coordinates in the affine chart with the final
coordinate eliminated. -/
def affineScaledBarycentric (d n : ℕ) :
    Fin (d + 1) → MvPolynomial (Fin d) ℝ :=
  Fin.snoc (fun i => MvPolynomial.X i)
    (MvPolynomial.C (n : ℝ) - ∑ i : Fin d, MvPolynomial.X i)

/-- At a degree-`n` lattice point, the affine coordinate polynomials recover
all `d + 1` scaled barycentric coordinates. -/
theorem eval_affineScaledBarycentric (d n : ℕ)
    (β : MultiIndex d n) (i : Fin (d + 1)) :
    MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ))
      (affineScaledBarycentric d n i) = (β.1 i : ℝ) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hsum := β.2
    rw [Fin.sum_univ_castSucc] at hsum
    have hsumR :
        (∑ j : Fin d, (β.1 j.castSucc : ℝ)) +
          (β.1 (Fin.last d) : ℝ) = (n : ℝ) := by
      exact_mod_cast hsum
    simp [affineScaledBarycentric]
    linarith
  · simp [affineScaledBarycentric]

/-- Every affine scaled barycentric coordinate has total degree at most one. -/
theorem totalDegree_affineScaledBarycentric_le (d n : ℕ)
    (i : Fin (d + 1)) :
    (affineScaledBarycentric d n i).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hsum :
        (∑ j : Fin d, (MvPolynomial.X j : MvPolynomial (Fin d) ℝ)).totalDegree ≤ 1 := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro j hj
      simp
    change (MvPolynomial.C (n : ℝ) -
      ∑ j : Fin d, (MvPolynomial.X j : MvPolynomial (Fin d) ℝ)).totalDegree ≤ 1
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by simp) hsum)
  · simp [affineScaledBarycentric]

/-- The simplex cardinal polynomial expressed in the `d` independent affine
coordinates. -/
def affineLatticeCardinalPolynomial (d n : ℕ) (α : MultiIndex d n) :
    MvPolynomial (Fin d) ℝ :=
  ∏ i : Fin (d + 1),
    normalizedDescPochhammerAt (affineScaledBarycentric d n i) (α.1 i)

/-- The affine cardinal polynomials have total degree at most `n`. -/
theorem totalDegree_affineLatticeCardinalPolynomial_le (d n : ℕ)
    (α : MultiIndex d n) :
    (affineLatticeCardinalPolynomial d n α).totalDegree ≤ n := by
  unfold affineLatticeCardinalPolynomial
  calc
    (∏ i : Fin (d + 1),
      normalizedDescPochhammerAt (affineScaledBarycentric d n i) (α.1 i)).totalDegree
        ≤ ∑ i : Fin (d + 1),
          (normalizedDescPochhammerAt
            (affineScaledBarycentric d n i) (α.1 i)).totalDegree := by
      simpa using MvPolynomial.totalDegree_finsetProd
        (Finset.univ : Finset (Fin (d + 1)))
        (fun i => normalizedDescPochhammerAt
          (affineScaledBarycentric d n i) (α.1 i))
    _ ≤ ∑ i : Fin (d + 1), (α.1 i : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact totalDegree_normalizedDescPochhammerAt_le
        (affineScaledBarycentric d n i) (α.1 i)
        (totalDegree_affineScaledBarycentric_le d n i)
    _ = n := α.2

/-- Each affine cardinal polynomial belongs to the correct degree-bounded
polynomial space in `d` variables. -/
theorem affineLatticeCardinalPolynomial_mem_restrictTotalDegree (d n : ℕ)
    (α : MultiIndex d n) :
    affineLatticeCardinalPolynomial d n α ∈
      MvPolynomial.restrictTotalDegree (Fin d) ℝ n := by
  rw [MvPolynomial.mem_restrictTotalDegree]
  exact totalDegree_affineLatticeCardinalPolynomial_le d n α

/-- Exact Kronecker-delta values on the degree-`n` simplex lattice. -/
theorem eval_affineLatticeCardinalPolynomial_eq_ite (d n : ℕ)
    (α β : MultiIndex d n) :
    MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ))
      (affineLatticeCardinalPolynomial d n α) = if α = β then 1 else 0 := by
  unfold affineLatticeCardinalPolynomial
  rw [map_prod]
  have hprod :
      (∏ i : Fin (d + 1),
        latticeFactor (α.1 i) (β.1 i)) =
        latticeCardinalValue
          (fun i => (α.1 i : ℕ)) (fun i => (β.1 i : ℕ)) := by
    rfl
  rw [show (∏ i : Fin (d + 1),
      MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ))
        (normalizedDescPochhammerAt (affineScaledBarycentric d n i) (α.1 i))) =
      ∏ i : Fin (d + 1), latticeFactor (α.1 i) (β.1 i) by
    apply Finset.prod_congr rfl
    intro i hi
    exact eval_normalizedDescPochhammerAt_nat
      (affineScaledBarycentric d n i) (α.1 i)
      (fun j : Fin d => (β.1 j.castSucc : ℝ)) (β.1 i)
      (eval_affineScaledBarycentric d n β i)]
  rw [hprod]
  exact latticeCardinalValue_eq_ite
    (fun i => (α.1 i : ℕ)) (fun i => (β.1 i : ℕ)) α.2 β.2

/-- The affine cardinal polynomial family is linearly independent in the
correct `d`-variable polynomial space. -/
theorem affineLatticeCardinalPolynomial_linearIndependent (d n : ℕ) :
    LinearIndependent ℝ (affineLatticeCardinalPolynomial d n) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h α
  have heval := congrArg
    (MvPolynomial.eval (fun j : Fin d => (α.1 j.castSucc : ℝ))) h
  simpa [eval_affineLatticeCardinalPolynomial_eq_ite] using heval

end AffineLatticePolynomial

end

end BernsteinObstacle
