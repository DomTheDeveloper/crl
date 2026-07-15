import FormalConjectures.ErdosProblems.«602»

open Set

namespace Erdos602

/--
A direct proof of the exact `erdos_602.variants.countable_index` statement.

At stage `i`, choose two points of `A i` outside the finite set of all points
chosen earlier.  Color every second chosen point blue and everything else red.
The globally fresh choices ensure that the first point selected for each `A i`
is never blue, while the second one is blue.

The countability and bounded-intersection assumptions are not needed for this
countable-index lemma; infinitude of every `A i` is sufficient.
-/
theorem countable_index_proof :
    answer(True) ↔
    ∀ (α : Type) (A : ℕ → Set α) (_ : ∀ i, (A i).Infinite)
      (_ : ∀ i, Countable (A i)) (_ : ∃ n, ∀ i j, (A i ∩ A j).ncard ≤ n),
      ∃ f : α → ℕ, ∀ i, ∃ x ∈ A i, ∃ y ∈ A i, f x ≠ f y := by
  show True ↔ _
  simp only [true_iff]
  intro α A hInfinite _hCountable _hInter
  classical

  have pair_exists (i : ℕ) (s : Finset α) :
      ∃ p : α × α,
        p.1 ∈ A i ∧ p.2 ∈ A i ∧ p.1 ∉ s ∧ p.2 ∉ s ∧ p.1 ≠ p.2 := by
    obtain ⟨x, hxA, hxs⟩ := (hInfinite i).exists_notMem_finset s
    obtain ⟨y, hyA, hyins⟩ := (hInfinite i).exists_notMem_finset (insert x s)
    have hyx : y ≠ x := by
      intro h
      subst y
      exact hyins (Finset.mem_insert_self x s)
    have hys : y ∉ s := by
      intro hy
      exact hyins (Finset.mem_insert_of_mem hy)
    exact ⟨(x, y), hxA, hyA, hxs, hys, fun hxy => hyx hxy.symm⟩

  let pick : ℕ → Finset α → α × α :=
    fun i s => Classical.choose (pair_exists i s)

  have pick_spec (i : ℕ) (s : Finset α) :
      (pick i s).1 ∈ A i ∧ (pick i s).2 ∈ A i ∧
      (pick i s).1 ∉ s ∧ (pick i s).2 ∉ s ∧ (pick i s).1 ≠ (pick i s).2 :=
    Classical.choose_spec (pair_exists i s)

  let used : ℕ → Finset α :=
    Nat.rec ∅ (fun i s => insert (pick i s).1 (insert (pick i s).2 s))
  let x : ℕ → α := fun i => (pick i (used i)).1
  let y : ℕ → α := fun i => (pick i (used i)).2

  have used_succ (i : ℕ) :
      used i.succ = insert (x i) (insert (y i) (used i)) := by
    rfl

  have hxA (i : ℕ) : x i ∈ A i := (pick_spec i (used i)).1
  have hyA (i : ℕ) : y i ∈ A i := (pick_spec i (used i)).2.1
  have hx_fresh (i : ℕ) : x i ∉ used i := (pick_spec i (used i)).2.2.1
  have hy_fresh (i : ℕ) : y i ∉ used i := (pick_spec i (used i)).2.2.2.1
  have hxy_same (i : ℕ) : x i ≠ y i := (pick_spec i (used i)).2.2.2.2

  have earlier_used : ∀ {j n : ℕ}, j < n → x j ∈ used n ∧ y j ∈ used n := by
    intro j n hj
    induction n with
    | zero => omega
    | succ n ih =>
        rw [used_succ]
        by_cases hjn : j = n
        · subst j
          exact ⟨Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
        · have hjlt : j < n := by omega
          obtain ⟨hxmem, hymem⟩ := ih hjlt
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxmem),
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hymem)⟩

  have cross_ne (i j : ℕ) : x i ≠ y j := by
    intro hij_eq
    rcases lt_trichotomy i j with hij | hij | hij
    · have hxmem := (earlier_used hij).1
      rw [hij_eq] at hxmem
      exact hy_fresh j hxmem
    · subst j
      exact hxy_same i hij_eq
    · have hymem := (earlier_used hij).2
      rw [← hij_eq] at hymem
      exact hx_fresh i hymem

  let f : α → ℕ := fun a => if ∃ j, a = y j then 1 else 0
  refine ⟨f, ?_⟩
  intro i
  refine ⟨x i, hxA i, y i, hyA i, ?_⟩
  have hx_not_blue : ¬ ∃ j, x i = y j := by
    rintro ⟨j, h⟩
    exact cross_ne i j h
  have hy_blue : ∃ j, y i = y j := ⟨i, rfl⟩
  simp [f, hx_not_blue, hy_blue]

#print axioms countable_index_proof

end Erdos602
