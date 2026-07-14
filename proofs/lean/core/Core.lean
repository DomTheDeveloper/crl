/-
  Core Lean 4 proofs — no Mathlib.
  These verify with the base Lean toolchain (fast) and are exactly the proofs
  that can run in the in-browser Lean (lean4.js / WASM), which ships only the
  Lean standard library.
-/

-- Addition is commutative (the site's runnable Lean proof for `add-comm`).
theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m

-- Multiplying by one.
theorem mul_one_r (n : Nat) : n * 1 = n := Nat.mul_one n

-- A concrete evaluation, checked by the kernel.
theorem two_add_two : 2 + 2 = 4 := rfl

-- Even + even is even (core version, closed by `omega`).
theorem even_plus_even (n m : Nat)
    (hn : ∃ a, n = 2 * a) (hm : ∃ b, m = 2 * b) : ∃ k, n + m = 2 * k := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb⟩ := hm
  exact ⟨a + b, by omega⟩
