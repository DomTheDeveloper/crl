import Mathlib

/-!
# The finite checkerboard four-direction packing model

This file defines the unreduced finite fractional LP and the corresponding
integral four-direction packing problem.  No line slopes other than rows,
columns, and the two principal diagonal families occur in these definitions.
-/

namespace Checkerboard

noncomputable section

/-- A point of the `n x n` grid. -/
abbrev GridPoint (n : ℕ) := Fin n × Fin n

/-- One checkerboard parity class. -/
def ParityPoint (n ε : ℕ) :=
  {p : GridPoint n // (p.1.val + p.2.val) % 2 = ε % 2}

/-- The four line families retained by the relaxation. -/
inductive FourLine (n : ℕ)
  | row (i : Fin n)
  | column (i : Fin n)
  | diagonalPos (i : Fin (2 * n + 1))
  | diagonalNeg (i : Fin (2 * n + 1))
  deriving DecidableEq, Fintype

/-- Incidence of a grid point with one of the four permitted line families.

The positive-diagonal key is `x+n-y`; the negative-diagonal key is `x+y`.
The ambient type `Fin (2*n+1)` deliberately contains a few unused keys, which
makes the definition uniform at `n=0`.
-/
def FourLine.Incident {n : ℕ} (p : GridPoint n) : FourLine n → Prop
  | .row i => p.2 = i
  | .column i => p.1 = i
  | .diagonalPos i => p.1.val + n - p.2.val = i.val
  | .diagonalNeg i => p.1.val + p.2.val = i.val

instance {n : ℕ} (p : GridPoint n) (l : FourLine n) :
    Decidable (FourLine.Incident p l) := inferInstance

/-- Total fractional load placed on a permitted line. -/
def lineLoad {n ε : ℕ} (x : ParityPoint n ε → ℝ) (l : FourLine n) : ℝ :=
  ∑ p : ParityPoint n ε, if FourLine.Incident p.1 l then x p else 0

/-- Feasibility for the finite four-direction fractional packing LP. -/
def FractionalFeasible {n ε : ℕ} (x : ParityPoint n ε → ℝ) : Prop :=
  (∀ p, 0 ≤ x p) ∧ (∀ l, lineLoad x l ≤ 2)

/-- Objective of the finite fractional packing LP. -/
def fractionalObjective {n ε : ℕ} (x : ParityPoint n ε → ℝ) : ℝ :=
  ∑ p, x p

/-- Set of objective values attained by feasible fractional packings. -/
def fractionalValueSet (n ε : ℕ) : Set ℝ :=
  {v | ∃ x : ParityPoint n ε → ℝ, FractionalFeasible x ∧ fractionalObjective x = v}

/-- The exact unreduced four-direction fractional optimum. -/
def L4 (n ε : ℕ) : ℝ := sSup (fractionalValueSet n ε)

lemma zero_fractionalFeasible (n ε : ℕ) :
    FractionalFeasible (fun _ : ParityPoint n ε => (0 : ℝ)) := by
  constructor
  · intro p
    simp
  · intro l
    simp [lineLoad]

lemma fractionalValueSet_nonempty (n ε : ℕ) :
    (fractionalValueSet n ε).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨fun _ => 0, zero_fractionalFeasible n ε, ?_⟩
  simp [fractionalObjective]

/-- Summing all row loads counts every point mass exactly once. -/
lemma fractionalObjective_eq_sum_rowLoads {n ε : ℕ}
    (x : ParityPoint n ε → ℝ) :
    fractionalObjective x = ∑ i : Fin n, lineLoad x (.row i) := by
  classical
  simp only [fractionalObjective, lineLoad]
  rw [Fintype.sum_comm]
  apply Fintype.sum_congr
  intro p
  simp [FourLine.Incident]

/-- Every feasible objective is at most the total row capacity `2n`. -/
lemma fractionalObjective_le_two_mul {n ε : ℕ}
    {x : ParityPoint n ε → ℝ} (hx : FractionalFeasible x) :
    fractionalObjective x ≤ 2 * n := by
  rw [fractionalObjective_eq_sum_rowLoads]
  calc
    (∑ i : Fin n, lineLoad x (.row i)) ≤ ∑ _i : Fin n, (2 : ℝ) := by
      exact Fintype.sum_le_sum fun i => hx.2 (.row i)
    _ = 2 * n := by simp

lemma fractionalValueSet_bddAbove (n ε : ℕ) :
    BddAbove (fractionalValueSet n ε) := by
  refine ⟨2 * n, ?_⟩
  intro v hv
  rcases hv with ⟨x, hx, rfl⟩
  exact fractionalObjective_le_two_mul hx

lemma L4_nonneg (n ε : ℕ) : 0 ≤ L4 n ε := by
  exact csSup_least (fractionalValueSet_nonempty n ε) fun v hv => by
    rcases hv with ⟨x, hx, rfl⟩
    exact Finset.sum_nonneg fun p _ => hx.1 p

lemma L4_le_two_mul (n ε : ℕ) : L4 n ε ≤ 2 * n := by
  exact csSup_le (fractionalValueSet_nonempty n ε) fun v hv => by
    rcases hv with ⟨x, hx, rfl⟩
    exact fractionalObjective_le_two_mul hx

/-- Integral feasibility for the same four fixed line families. -/
def IntegralFeasible {n ε : ℕ} (s : Finset (ParityPoint n ε)) : Prop :=
  ∀ l, (s.filter fun p => FourLine.Incident p.1 l).card ≤ 2

lemma empty_integralFeasible (n ε : ℕ) :
    IntegralFeasible (∅ : Finset (ParityPoint n ε)) := by
  intro l
  simp [IntegralFeasible]

/-- Exact integral optimum for the four fixed directions only. -/
def I4 (n ε : ℕ) : ℕ :=
  ((Finset.univ.powerset.filter fun s : Finset (ParityPoint n ε) => IntegralFeasible s).sup
    Finset.card)

/-- Odd-side fat-class fractional optimum. -/
def oddFatL4 (m : ℕ) : ℝ := L4 (2 * m + 1) 0

/-- Odd-side thin-class fractional optimum. -/
def oddThinL4 (m : ℕ) : ℝ := L4 (2 * m + 1) 1

/-- Even-side fractional optimum; the other parity class is reflection-equivalent. -/
def evenL4 (m : ℕ) : ℝ := L4 (2 * m) 0

end

end Checkerboard
