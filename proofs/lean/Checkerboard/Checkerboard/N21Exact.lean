import Checkerboard.N21Boolean
import Checkerboard.Finite21Lower

/-!
# Exact 21×21 checkerboard maxima

This file connects the kernel-checked integer dual profiles and finite Boolean
closures to arbitrary monochromatic no-three-in-line sets.
-/

namespace Checkerboard

private theorem n21p0_selectedPoints_eq
    (s : Finset (Point 21))
    (hcolor : Monochromatic 0 s)
    (hslack : ∀ p ∈ s, coverage n21p0Weight p - 75 ≤ 1) :
    let x : Fin 136 → Bool := fun i => decide (n21p0Point i ∈ s)
    selectedPoints n21p0Point x = s := by
  dsimp
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    have hx := (Finset.mem_filter.mp hi).2
    simpa using hx
  · intro hp
    obtain ⟨i, hi⟩ := n21p0Point_surjective p
      (hcolor ⟨p, hp⟩) (hslack p hp)
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ i
    · simpa [hi] using hp

private theorem n21p1_selectedPoints_eq
    (s : Finset (Point 21))
    (hcolor : Monochromatic 1 s)
    (hslack : ∀ p ∈ s, coverage n21p1Weight p - 48 ≤ 0) :
    let x : Fin 132 → Bool := fun i => decide (n21p1Point i ∈ s)
    selectedPoints n21p1Point x = s := by
  dsimp
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    have hx := (Finset.mem_filter.mp hi).2
    simpa using hx
  · intro hp
    obtain ⟨i, hi⟩ := n21p1Point_surjective p
      (hcolor ⟨p, hp⟩) (hslack p hp)
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ i
    · simpa [hi] using hp

private theorem n21p0_avoids
    (s : Finset (Point 21)) (hntil : NoThreeInLine s)
    (x : Fin 136 → Bool)
    (hx : ∀ i, x i = true ↔ n21p0Point i ∈ s) :
    avoidsCollinearTriples n21p0Point x := by
  intro t ht
  have htriple := (Finset.mem_filter.mp ht).2
  rcases htriple with ⟨hab, hbc, hdet⟩
  by_contra h
  push_neg at h
  rcases h with ⟨ha, hb, hc⟩
  have haS : n21p0Point t.a ∈ s := (hx t.a).mp ha
  have hbS : n21p0Point t.b ∈ s := (hx t.b).mp hb
  have hcS : n21p0Point t.c ∈ s := (hx t.c).mp hc
  have habI : t.a ≠ t.b := by
    intro e
    exact (Nat.ne_of_lt hab) (congrArg Fin.val e)
  have hacI : t.a ≠ t.c := by
    intro e
    have : t.a.1 = t.c.1 := congrArg Fin.val e
    omega
  have hbcI : t.b ≠ t.c := by
    intro e
    exact (Nat.ne_of_lt hbc) (congrArg Fin.val e)
  have habP : n21p0Point t.a ≠ n21p0Point t.b := by
    intro e
    exact habI (n21p0Point_injective e)
  have hacP : n21p0Point t.a ≠ n21p0Point t.c := by
    intro e
    exact hacI (n21p0Point_injective e)
  have hbcP : n21p0Point t.b ≠ n21p0Point t.c := by
    intro e
    exact hbcI (n21p0Point_injective e)
  exact hntil ⟨n21p0Point t.a, haS⟩ ⟨n21p0Point t.b, hbS⟩
    ⟨n21p0Point t.c, hcS⟩
    (by intro e; exact habP (congrArg Subtype.val e))
    (by intro e; exact hacP (congrArg Subtype.val e))
    (by intro e; exact hbcP (congrArg Subtype.val e)) hdet

private theorem n21p1_avoids
    (s : Finset (Point 21)) (hntil : NoThreeInLine s)
    (x : Fin 132 → Bool)
    (hx : ∀ i, x i = true ↔ n21p1Point i ∈ s) :
    avoidsCollinearTriples n21p1Point x := by
  intro t ht
  have htriple := (Finset.mem_filter.mp ht).2
  rcases htriple with ⟨hab, hbc, hdet⟩
  by_contra h
  push_neg at h
  rcases h with ⟨ha, hb, hc⟩
  have haS : n21p1Point t.a ∈ s := (hx t.a).mp ha
  have hbS : n21p1Point t.b ∈ s := (hx t.b).mp hb
  have hcS : n21p1Point t.c ∈ s := (hx t.c).mp hc
  have habI : t.a ≠ t.b := by
    intro e
    exact (Nat.ne_of_lt hab) (congrArg Fin.val e)
  have hacI : t.a ≠ t.c := by
    intro e
    have : t.a.1 = t.c.1 := congrArg Fin.val e
    omega
  have hbcI : t.b ≠ t.c := by
    intro e
    exact (Nat.ne_of_lt hbc) (congrArg Fin.val e)
  have habP : n21p1Point t.a ≠ n21p1Point t.b := by
    intro e
    exact habI (n21p1Point_injective e)
  have hacP : n21p1Point t.a ≠ n21p1Point t.c := by
    intro e
    exact hacI (n21p1Point_injective e)
  have hbcP : n21p1Point t.b ≠ n21p1Point t.c := by
    intro e
    exact hbcI (n21p1Point_injective e)
  exact hntil ⟨n21p1Point t.a, haS⟩ ⟨n21p1Point t.b, hbS⟩
    ⟨n21p1Point t.c, hcS⟩
    (by intro e; exact habP (congrArg Subtype.val e))
    (by intro e; exact hacP (congrArg Subtype.val e))
    (by intro e; exact hbcP (congrArg Subtype.val e)) hdet

/-- Exact upper bound for the fat color class of the 21-board. -/
theorem n21p0_upper (s : Finset (Point 21))
    (hcolor : Monochromatic 0 s) (hntil : NoThreeInLine s) : s.card ≤ 32 := by
  have hcover : ∀ p : ↥s, 75 ≤ coverage n21p0Weight p.1 :=
    fun p => n21p0_cover p.1 (hcolor p)
  have hcoarse := certificate_bound n21p0Weight hcover hntil
  rw [n21p0_cost] at hcoarse
  have hle : s.card ≤ 33 := by omega
  by_contra hnot
  have hcard : s.card = 33 := by omega
  have hidentity := natCertificateBudget_identity n21p0Weight s hcover hntil
  rw [n21p0_cost, hcard] at hidentity
  have hbudget : natCertificateBudget n21p0Weight s = 1 := by omega
  have hslack : ∀ p ∈ s, coverage n21p0Weight p - 75 ≤ 1 := by
    intro p hp
    have h := natPointSlack_le_budget n21p0Weight s hcover hp
    omega
  let x : Fin 136 → Bool := fun i => decide (n21p0Point i ∈ s)
  have hx : ∀ i, x i = true ↔ n21p0Point i ∈ s := by
    intro i
    simp [x]
  have hselected := n21p0_selectedPoints_eq s hcolor hslack
  change selectedPoints n21p0Point x = s at hselected
  have havoids := n21p0_avoids s hntil x hx
  have hbudgetX :
      natCertificateBudget n21p0Weight (selectedPoints n21p0Point x) = 1 := by
    rw [hselected]
    exact hbudget
  have hbound := n21p0_boolean_bound x havoids hbudgetX
  have hcardImage := Finset.card_image_of_injective (selectedIndices x)
    n21p0Point_injective
  have hselectedCard : (selectedIndices x).card = s.card := by
    calc
      (selectedIndices x).card = (selectedPoints n21p0Point x).card :=
        hcardImage.symm
      _ = s.card := congrArg Finset.card hselected
  rw [hselectedCard] at hbound
  omega

/-- Exact upper bound for the thin color class of the 21-board. -/
theorem n21p1_upper (s : Finset (Point 21))
    (hcolor : Monochromatic 1 s) (hntil : NoThreeInLine s) : s.card ≤ 32 := by
  have hcover : ∀ p : ↥s, 48 ≤ coverage n21p1Weight p.1 :=
    fun p => n21p1_cover p.1 (hcolor p)
  have hcoarse := certificate_bound n21p1Weight hcover hntil
  rw [n21p1_cost] at hcoarse
  have hle : s.card ≤ 33 := by omega
  by_contra hnot
  have hcard : s.card = 33 := by omega
  have hidentity := natCertificateBudget_identity n21p1Weight s hcover hntil
  rw [n21p1_cost, hcard] at hidentity
  have hbudget : natCertificateBudget n21p1Weight s = 0 := by omega
  have hslack : ∀ p ∈ s, coverage n21p1Weight p - 48 ≤ 0 := by
    intro p hp
    have h := natPointSlack_le_budget n21p1Weight s hcover hp
    omega
  let x : Fin 132 → Bool := fun i => decide (n21p1Point i ∈ s)
  have hx : ∀ i, x i = true ↔ n21p1Point i ∈ s := by
    intro i
    simp [x]
  have hselected := n21p1_selectedPoints_eq s hcolor hslack
  change selectedPoints n21p1Point x = s at hselected
  have havoids := n21p1_avoids s hntil x hx
  have hbudgetX :
      natCertificateBudget n21p1Weight (selectedPoints n21p1Point x) = 0 := by
    rw [hselected]
    exact hbudget
  have hbound := n21p1_boolean_bound x havoids hbudgetX
  have hcardImage := Finset.card_image_of_injective (selectedIndices x)
    n21p1Point_injective
  have hselectedCard : (selectedIndices x).card = s.card := by
    calc
      (selectedIndices x).card = (selectedPoints n21p1Point x).card :=
        hcardImage.symm
      _ = s.card := congrArg Finset.card hselected
  rw [hselectedCard] at hbound
  omega

/-- `D_mono(21,0)=32`, stated as an exact maximum theorem. -/
theorem exact_n21_p0 : IsExactMaximum 21 0 32 := by
  constructor
  · exact n21p0_lower
  · intro s hcolor hntil
    exact n21p0_upper s hcolor hntil

/-- `D_mono(21,1)=32`, stated as an exact maximum theorem. -/
theorem exact_n21_p1 : IsExactMaximum 21 1 32 := by
  constructor
  · exact n21p1_lower
  · intro s hcolor hntil
    exact n21p1_upper s hcolor hntil

end Checkerboard
