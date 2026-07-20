import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace BernsteinObstacle

/-!
# Sequential Mosco convergence

The analytical theorem in the manuscript uses strong recovery and weak limit
closure.  This file records that exact quantifier structure for normed spaces,
using continuous linear functionals to define weak sequential convergence.
It is infrastructure for the later Sobolev/FEM recovery proof; it does not by
itself assert that the Bernstein finite-element cones satisfy the definition.
-/

section Mosco

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strong convergence of a sequence in the norm topology. -/
def StronglyConverges (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x)

/-- Weak sequential convergence, tested against every continuous linear
functional. -/
def WeaklyConverges (u : ℕ → E) (x : E) : Prop :=
  ∀ φ : E →L[ℝ] ℝ, Tendsto (fun n => φ (u n)) atTop (𝓝 (φ x))

/-- Sequential Mosco convergence of moving sets `K n` to `K`.  The first field
is the strong recovery condition.  The second is the weak limit condition along
all strictly increasing mesh-index subsequences. -/
structure MoscoConverges (K : ℕ → Set E) (Klim : Set E) : Prop where
  recovery :
    ∀ x ∈ Klim, ∃ u : ℕ → E,
      (∀ n, u n ∈ K n) ∧ StronglyConverges u x
  weak_limit :
    ∀ (φ : ℕ → ℕ), StrictMono φ,
      ∀ (u : ℕ → E) (x : E),
        (∀ n, u n ∈ K (φ n)) → WeaklyConverges u x → x ∈ Klim

/-- Weak sequential closedness of one fixed feasible set. -/
def WeaklySequentiallyClosed (K : Set E) : Prop :=
  ∀ (u : ℕ → E) (x : E),
    (∀ n, u n ∈ K) → WeaklyConverges u x → x ∈ K

/-- A constant family Mosco-converges to itself whenever the set is weakly
sequentially closed. -/
theorem moscoConverges_const_self (K : Set E)
    (hK : WeaklySequentiallyClosed K) :
    MoscoConverges (fun _ => K) K := by
  constructor
  · intro x hx
    refine ⟨fun _ => x, ?_, ?_⟩
    · intro n
      exact hx
    · exact tendsto_const_nhds
  · intro φ hφ u x hu hweak
    exact hK u x (fun n => hu n) hweak

/-- The two defining conditions can be extracted without unfolding the
structure at use sites. -/
theorem mosco_recovery {K : ℕ → Set E} {Klim : Set E}
    (hM : MoscoConverges K Klim) {x : E} (hx : x ∈ Klim) :
    ∃ u : ℕ → E, (∀ n, u n ∈ K n) ∧ StronglyConverges u x :=
  hM.recovery x hx

/-- Weak limits of feasible subsequences belong to the Mosco limit set. -/
theorem mosco_weak_limit {K : ℕ → Set E} {Klim : Set E}
    (hM : MoscoConverges K Klim)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (u : ℕ → E) (x : E)
    (hu : ∀ n, u n ∈ K (φ n))
    (hweak : WeaklyConverges u x) :
    x ∈ Klim :=
  hM.weak_limit φ hφ u x hu hweak

end Mosco

end BernsteinObstacle
