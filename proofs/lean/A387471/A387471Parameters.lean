import A387471Converse

/-!
# Explicit duplicate-free parameter sets for A387471
-/

open Finset

namespace A387471

/-- One of the six ordered permutations of a triple. -/
def permTripleNat (σ : Fin 6) (a b c : ℕ) : Triple :=
  match σ.val with
  | 0 => (a, b, c)
  | 1 => (a, c, b)
  | 2 => (b, a, c)
  | 3 => (b, c, a)
  | 4 => (c, a, b)
  | 5 => (c, b, a)
  | _ => (a, b, c)

lemma permTripleNat_perm3 (σ : Fin 6) (a b c : ℕ) :
    Perm3 (permTripleNat σ a b c).1 (permTripleNat σ a b c).2.1
      (permTripleNat σ a b c).2.2 a b c := by
  fin_cases σ <;> simp [permTripleNat, Perm3]

abbrev OrdinaryParam (n : ℕ) := Fin (n - 1) × Fin 6

/-- The small entry `r`, ranging through `1,…,n-1`. -/
def ordinaryR {n : ℕ} (p : OrdinaryParam n) : ℕ := p.1.val + 1

lemma ordinaryR_bounds {n : ℕ} (p : OrdinaryParam n) :
    1 ≤ ordinaryR p ∧ ordinaryR p < n := by
  simp [ordinaryR]
  omega

/-- Six permutations of `(r,n,2n-r)`, with `1≤r<n`. -/
def ordinaryParamTriple (n : ℕ) (p : OrdinaryParam n) : Triple :=
  permTripleNat p.2 (ordinaryR p) n (2 * n - ordinaryR p)

/-- The ordinary noncentral parameterization is injective. -/
theorem ordinaryParamTriple_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (ordinaryParamTriple n) := by
  rintro ⟨r, σ⟩ ⟨s, τ⟩ h
  fin_cases σ <;> fin_cases τ <;>
    simp [ordinaryParamTriple, ordinaryR, permTripleNat] at h ⊢ <;> omega

/-- All noncentral ordinary triples. -/
def ordinaryNoncentral (n : ℕ) : Finset Triple :=
  Finset.univ.image (ordinaryParamTriple n)

/-- The complete ordinary set, including `(n,n,n)`. -/
def ordinarySet (n : ℕ) : Finset Triple :=
  insert (n, n, n) (ordinaryNoncentral n)

lemma central_not_mem_ordinaryNoncentral {n : ℕ} (hn : 0 < n) :
    (n, n, n) ∉ ordinaryNoncentral n := by
  intro h
  rcases Finset.mem_image.mp h with ⟨⟨r, σ⟩, -, heq⟩
  fin_cases σ <;>
    simp [ordinaryParamTriple, ordinaryR, permTripleNat] at heq <;> omega

/-- Exact ordinary cardinality. -/
theorem card_ordinaryNoncentral {n : ℕ} (hn : 0 < n) :
    (ordinaryNoncentral n).card = 6 * (n - 1) := by
  rw [ordinaryNoncentral,
    Finset.card_image_of_injective Finset.univ (ordinaryParamTriple_injective hn)]
  simp [OrdinaryParam]
  omega

/-- Exact ordinary cardinality, including the center. -/
theorem card_ordinarySet {n : ℕ} (hn : 0 < n) :
    (ordinarySet n).card = 6 * (n - 1) + 1 := by
  rw [ordinarySet, Finset.card_insert_of_notMem (central_not_mem_ordinaryNoncentral hn),
    card_ordinaryNoncentral hn]

abbrev ExceptionalParam := Fin 2 × Fin 6

/-- The two exceptional unordered base triples and all six orderings. -/
def exceptionalParamTriple (q : ℕ) (p : ExceptionalParam) : Triple :=
  match p.1.val with
  | 0 => permTripleNat p.2 q (7 * q) (8 * q)
  | 1 => permTripleNat p.2 (2 * q) (3 * q) (9 * q)
  | _ => permTripleNat p.2 q (7 * q) (8 * q)

/-- The twelve exceptional triples are distinct when `q>0`. -/
theorem exceptionalParamTriple_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (exceptionalParamTriple q) := by
  rintro ⟨f, σ⟩ ⟨g, τ⟩ h
  fin_cases f <;> fin_cases g <;> fin_cases σ <;> fin_cases τ <;>
    simp [exceptionalParamTriple, permTripleNat] at h ⊢ <;> omega

/-- The explicit exceptional set at scale `q`. -/
def exceptionalSet (q : ℕ) : Finset Triple :=
  Finset.univ.image (exceptionalParamTriple q)

/-- Exact exceptional cardinality. -/
theorem card_exceptionalSet {q : ℕ} (hq : 0 < q) :
    (exceptionalSet q).card = 12 := by
  rw [exceptionalSet,
    Finset.card_image_of_injective Finset.univ (exceptionalParamTriple_injective hq)]
  simp [ExceptionalParam]

#print axioms ordinaryParamTriple_injective
#print axioms card_ordinarySet
#print axioms exceptionalParamTriple_injective
#print axioms card_exceptionalSet

end A387471
