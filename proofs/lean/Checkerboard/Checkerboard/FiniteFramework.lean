import Mathlib


/-!
# Finite checkerboard framework

Basic definitions and finite-sum inequalities used by the complete `2n - 4`
checkerboard theorem. Coordinates are doubled when centered, so the even-board
case never requires hidden half-integer casts.
-/

namespace Checkerboard

open scoped BigOperators

abbrev Board (n : ℕ) := Fin n × Fin n

def xCoord {n : ℕ} (p : Board n) : ℕ := p.1.1

def yCoord {n : ℕ} (p : Board n) : ℕ := p.2.1

def pointColor {n : ℕ} (p : Board n) : ℕ := (xCoord p + yCoord p) % 2

def Moinchromatic {n : ℕ} (ε : ℕ) (S : Finset (Board n)) : Prop :=
  ∀ p ∈ S, pointColor p = ε % 2

def fiberCard {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (b : β) : ℕ :=
  (S.filter fun a => f a = b).card

def centered2 (n : ℕ) (i : Fin n) : ℤ :=
  2 * (i.1 : ℤ) - ((n : ℤ) - 1)

def centered2Nat (n i : ℕ) : ℝ :=
  2 * (i : ℝ) - ((n : ℝ) - 1)

theorem weightedCauchy {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * z i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * z i ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun i => w i * z i)
    (f := w)
    (g := fun i => w i * z i ^ 2) hw ?_ ?_
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    ring

theorem sum_fiberCard {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∑ b : β, fiberCard S f b = S.card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)

theorem sum_fiberCard_mul {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) :
    ∑ b : β, (fiberCard S f b : ℝ) * g b = ∑ a ∈ S, g (f a) := by
  classical
  rw [← Finset.sum_fiberwise' S f g]
  apply Finset.sum_congr rfl
  intro b hb
  simp [fiberCard, nsmul_eq_mul]

theorem sum_fiberCard_range {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (N : ℕ)
    (hf : ∀ a ∈ S, f a < N) :
    ∑ b in Finset.range N, fiberCard S f b = S.card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise
    (t := Finset.range N) (by simpa using hf)

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
