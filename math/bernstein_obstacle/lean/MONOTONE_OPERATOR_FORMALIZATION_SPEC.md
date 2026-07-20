# Lean specification: strongly monotone operator variational inequalities

## Status

This is a theorem-correspondence and implementation specification.  It is not a
claim that the operator theorem already compiles in Lean.

The existing V5 files formalize metric-projection variational inequalities.
The V6 target should add a genuinely operator-valued VI layer and prove the
inner-cone Falk estimate used in `GRAND_THEOREM_V6.md`.

---

## 1. Recommended representation

For the first formal milestone, work in a real inner-product space and use the
Riesz-identified operator form

```lean
A : E -> E
f : E
```

rather than beginning with continuous dual spaces.  This is sufficient to
formalize the algebraic heart of the theorem:

```lean
inner (A u - f) (v - u) >= 0
```

A later layer may transport the theorem to continuous linear functionals by a
Riesz isometry.

Suggested variables:

```lean
variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
```

---

## 2. Core definitions

```lean
def IsOperatorVISolution
    (K : Set E) (A : E -> E) (f u : E) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪A u - f, v - u⟫_ℝ
```

```lean
def StronglyMonotone
    (A : E -> E) (alpha : ℝ) : Prop :=
  ∀ x y,
    alpha * ‖x - y‖ ^ 2
      ≤ ⟪A x - A y, x - y⟫_ℝ
```

```lean
def LipschitzOperator
    (A : E -> E) (L : ℝ) : Prop :=
  ∀ x y, ‖A x - A y‖ ≤ L * ‖x - y‖
```

The production implementation should reuse mathlib predicates when their
signatures align cleanly, but the theorem statement should remain readable and
correspond exactly to the manuscript.

---

## 3. First terminal theorem: inner-cone Falk inequality

Target statement, modulo syntax and assumptions that `alpha>0`, `L>=0`:

```lean
theorem operator_vi_innerCone_falk
    (K Kh : Set E)
    (A : E -> E) (f u uh vh : E)
    (hsub : Kh ⊆ K)
    (hu : IsOperatorVISolution K A f u)
    (huh : IsOperatorVISolution Kh A f uh)
    (hvh : vh ∈ Kh)
    (hmono : StronglyMonotone A alpha)
    (hlip : LipschitzOperator A L) :
    alpha * ‖uh - u‖ ^ 2
      ≤ L * ‖uh - u‖ * ‖vh - u‖
        + ⟪A u - f, vh - u⟫_ℝ := by
  ...
```

Proof map:

1. use `hmono uh u`;
2. obtain `uh ∈ K` from `hsub huh.1`;
3. use the continuous VI at `uh`;
4. use the discrete VI at `vh`;
5. rewrite
   `uh-u = (uh-vh)+(vh-u)`;
6. discard the nonpositive discrete term;
7. apply real Cauchy--Schwarz and `hlip uh u`.

No convexity, closure, existence theorem, or symmetry is needed for this
algebraic estimate once the two solutions are supplied.

---

## 4. Squared-error theorem

Target:

```lean
theorem operator_vi_innerCone_error_sq
    ... :
    ‖uh - u‖ ^ 2
      ≤ (L ^ 2 / alpha ^ 2) * ‖vh - u‖ ^ 2
        + (2 / alpha) * ⟪A u - f, vh - u⟫_ℝ := by
  ...
```

Proof obligation:

- apply the Falk inequality;
- use Young's inequality
  `L*a*b <= alpha/2*a^2 + L^2/(2*alpha)*b^2`;
- divide only after recording `0 < alpha`.

The theorem should preserve the residual term instead of replacing it by an
absolute value.  Feasibility makes the residual nonnegative and its sharp
contact estimate is essential to the `3/2` rate.

---

## 5. Recovery-to-convergence theorem

A sequence-level theorem should assume:

```lean
Kh : ℕ -> Set E
uh vh : ℕ -> E
```

with:

- `Kh n ⊆ K`;
- `vh n ∈ Kh n`;
- `vh n -> u`;
- `uh n` solves the operator VI on `Kh n`.

The result:

```lean
Tendsto uh atTop (𝓝 u)
```

should follow from the squared-error theorem and continuity of

```lean
v ↦ ⟪A u - f, v - u⟫_ℝ.
```

This theorem is the nonlinear analogue of the V5 nested recovery theorem, but
it must not require nestedness.

---

## 6. Quantitative rate-composition theorem

Formalize a scalar theorem corresponding to:

```text
approximation <= Capp * rho
residual      <= Cres * rho^2
--------------------------------
solution error <= C * rho
```

A useful initial statement can remain squared:

```lean
‖uh - u‖ ^ 2
  ≤ ((L^2 / alpha^2) * Capp^2 + (2 / alpha) * Cres) * rho^2
```

This avoids unnecessary square-root algebra.  A second theorem may derive a
norm bound using nonnegativity and `Real.sqrt`.

---

## 7. Same-cone perturbation theorem

Definitions:

```lean
uExact : IsOperatorVISolution K A f u
uPert  : IsOperatorVISolution K Aδ fδ uδ
```

Assume `Aδ` is `alphaδ`-strongly monotone.  Target:

```lean
alphaδ * ‖uδ - u‖
  ≤ ‖(A u - Aδ u) - (f - fδ)‖
```

or the squared equivalent.  The proof tests the two inequalities against one
another and uses Cauchy--Schwarz.

This theorem does not require Lipschitz continuity or symmetry.

---

## 8. Correspondence with the physical theorem

The Lean operator theorem proves only the universal VI endgame.  The following
remain separate analytical inputs:

1. physical `H_0^1` and `H^{-1}` realization;
2. Bernstein positive smooth recovery;
3. local free-boundary localization;
4. clipping repair norm;
5. multiplier density and support;
6. `O(h_Gamma^3)` residual estimate.

The final manuscript theorem is obtained by instantiating the abstract Lean
estimate with these analytical data.

---

## 9. Required audit declarations

The terminal audit should print axioms for at least:

```text
BernsteinObstacle.operator_vi_innerCone_falk
BernsteinObstacle.operator_vi_innerCone_error_sq
BernsteinObstacle.operatorVISolutions_strongConvergence_of_recovery
BernsteinObstacle.operator_vi_rate_compose
BernsteinObstacle.operator_vi_sameCone_perturbation
```

The audit must reject `sorryAx` and preserve the pinned mathlib toolchain.

---

## 10. No-verification warning

No file produced from this specification should be described as verified until
it has been run through AXLE or the exact pinned local Lean environment and the
actual build and axiom transcripts have been inspected.
