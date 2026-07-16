import Mathlib

/-!
# Finite checkerboard framework

Basic definitions and finite-sum inequalities used by the complete `2n - 4`
checkerboard theorem.  Coordinates are doubled when centered, so the even-board
case never requires hidden half-integer casts.
-/

namespace Checkerboard

open scoped BigOperators

abbrev Board (n : ℕ) := Fin n × Fin n

/-- The natural x-coordinate of a board point. -/
def xCoord {n : ℕ} (p : Board n) : ℕ := p.1.1

/-- The natural y-coordinate of a board point. -/
def yCoord {n : ℕ} (p : Board n) : ℕ := p.2.1

/-- Checkerboard parity. -/
def pointColor {n : ℕ} (p : Board n) : ℕ := (xCoord p + yCoord p) % 2

/-- A finite set lies in one checkerboard color class. -/
def Monochromatic {n : ℕ} (ε : ℕ) (S : Finset (Board n)) : Prop :=
  ∀ p ∈ S, pointColor p = ε % 2

/-- Number of selected points in a fiber of `f`. -/
def fiberCard {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (b : β) : ℕ :=
  (S.filter fun a => f a = b).card

/-- The doubled centered coordinate `2i-(n-1)`. -/
def centered2 (n : ℕ) (i : Fin n) : ℤ :=
  2 * (i.1 : ℤ) - ((n : ℤ) - 1)

/-- The doubled centered coordinate on a natural index. -/
def centered2Nat (n i : ℕ) : ℝ :=
  2 * (i : ℝ) - ((n : ℝ) - 1)

/-- Weighted Cauchy--Schwarz in exactly the form needed for deficit moments. -/
theorem weightedCauchy {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * z i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * z i ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => w i * z i)
    (f := w)
    (g := fun i => w i * z i ^ 2) hw ?_ ?_
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    ring

/-- Sum of all fiber cardinalities over a finite codomain. -/
theorem sum_fiberCard {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∑ b : β, fiberCard S f b = S.card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)

/-- A fiberwise weighted sum is the original pointwise sum. -/
theorem sum_fiberCard_mul {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) :
    ∑ b : β, (fiberCard S f b : ℝ) * g b = ∑ a ∈ S, g (f a) := by
  classical
  rw [← Finset.sum_fiberwise' S f g]
  apply Finset.sum_congr rfl
  intro b hb
  simp [fiberCard, nsmul_eq_mul]

/-- Sum of fiber cardinalities when all images lie in a natural range. -/
theorem sum_fiberCard_range {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (N : ℕ)
    (hf : ∀ a ∈ S, f a < N) :
    ∑ b in Finset.range N, fiberCard S f b = S.card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise
    (t := Finset.range N) (by simpa using hf)

/-- Fiberwise weighted sum over a natural range. -/
theorem sum_fiberCard_mul_range {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (N : ℕ) (g : ℕ → ℝ)
    (hf : ∀ a ∈ S, f a < N) :
    ∑ b in Finset.range N, (fiberCard S f b : ℝ) * g b =
      ∑ a ∈ S, g (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (s := S) (t := Finset.range N)
    (g := f) (by simpa using hf) g]
  apply Finset.sum_congr rfl
  intro b hb
  simp [fiberCard, nsmul_eq_mul]

end Checkerboard
