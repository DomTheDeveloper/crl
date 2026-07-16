import Checkerboard.Model

/-!
# Exact budget identity for integer principal-line certificates
-/

namespace Checkerboard

open scoped BigOperators

/-- Unused weighted capacity over all principal lines. -/
def natCertificateDeficit {n : ℕ} (weight : PrincipalLine n → ℕ)
    (s : Finset (Point n)) : ℕ :=
  ∑ line : PrincipalLine n,
    (2 - (s.filter (OnLine line)).card) * weight line

/-- Point slack plus unused line capacity. -/
def natCertificateBudget {n q : ℕ} (weight : PrincipalLine n → ℕ)
    (s : Finset (Point n)) : ℕ :=
  (∑ p ∈ s, (coverage weight p - q)) + natCertificateDeficit weight s

private theorem sum_indicator_eq_card_filter_nat {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] (w : ℕ) :
    (∑ a ∈ s, if P a then w else 0) = (s.filter P).card * w := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hP : P a <;> simp [ha, hP, ih, Nat.add_mul]

private theorem nat_double_count {n : ℕ} (s : Finset (Point n))
    (weight : PrincipalLine n → ℕ) :
    (∑ p ∈ s, coverage weight p) =
      ∑ line : PrincipalLine n,
        (s.filter (OnLine line)).card * weight line := by
  calc
    (∑ p ∈ s, coverage weight p) =
        ∑ p ∈ s, ∑ line : PrincipalLine n,
          if OnLine line p then weight line else 0 := by rfl
    _ = ∑ line : PrincipalLine n, ∑ p ∈ s,
          if OnLine line p then weight line else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ line : PrincipalLine n,
          (s.filter (OnLine line)).card * weight line := by
          apply Finset.sum_congr rfl
          intro line _
          exact sum_indicator_eq_card_filter_nat s (OnLine line) (weight line)

private theorem line_capacity_identity {n : ℕ}
    (weight : PrincipalLine n → ℕ) (s : Finset (Point n))
    (hntil : NoThreeInLine s) :
    (∑ line : PrincipalLine n,
        (s.filter (OnLine line)).card * weight line) +
      natCertificateDeficit weight s = certificateCost weight := by
  unfold natCertificateDeficit certificateCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro line _
  have hcard := principalLine_card_le_two hntil line
  omega

/-- Exact integer identity
`q|s| + point-slack + line-deficit = certificateCost`. -/
theorem natCertificateBudget_identity {n q : ℕ}
    (weight : PrincipalLine n → ℕ) (s : Finset (Point n))
    (hcover : ∀ p : ↥s, q ≤ coverage weight p)
    (hntil : NoThreeInLine s) :
    q * s.card + natCertificateBudget weight s = certificateCost weight := by
  have hcoverage :
      (∑ p ∈ s, coverage weight p) =
        q * s.card + ∑ p ∈ s, (coverage weight p - q) := by
    calc
      (∑ p ∈ s, coverage weight p) =
          ∑ p ∈ s, (q + (coverage weight p - q)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Nat.add_sub_of_le (hcover ⟨p, hp⟩)]
      _ = (∑ _p ∈ s, q) + ∑ p ∈ s, (coverage weight p - q) := by
            rw [Finset.sum_add_distrib]
      _ = q * s.card + ∑ p ∈ s, (coverage weight p - q) := by
            simp [Nat.mul_comm]
  have hline := line_capacity_identity weight s hntil
  rw [← nat_double_count s weight] at hline
  unfold natCertificateBudget
  omega

/-- Every selected point's slack is bounded by the total integer budget. -/
theorem natPointSlack_le_budget {n q : ℕ}
    (weight : PrincipalLine n → ℕ) (s : Finset (Point n))
    (hcover : ∀ p : ↥s, q ≤ coverage weight p)
    {p : Point n} (hp : p ∈ s) :
    coverage weight p - q ≤ natCertificateBudget weight s := by
  have hsingle : coverage weight p - q ≤
      ∑ z ∈ s, (coverage weight z - q) := by
    apply Finset.single_le_sum
    · intro z hz
      exact Nat.zero_le _
    · exact hp
  unfold natCertificateBudget
  omega

end Checkerboard
