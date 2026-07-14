# Formal Lean proof of OEIS A317940 nonnegativity

## Summary

I have a complete Lean 4 proof of the OEIS A317940 conjecture formalized on the `auto_oeis` branch as

```lean
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) :
    A317940_f n ≥ 0
```

The proof establishes the stronger statement that `A317940_f n > 0` for every `n > 0`.

## Proof links

- Complete Lean source: https://github.com/DomTheDeveloper/test-expo-app/blob/e48e2ec5e9bf036b490776650dfbe1e2127b8275/A317940/A317940.lean
- Human-readable proof: https://github.com/DomTheDeveloper/test-expo-app/blob/e48e2ec5e9bf036b490776650dfbe1e2127b8275/A317940/HUMAN_PROOF.md
- Proof-host draft PR and discussion: https://github.com/DomTheDeveloper/test-expo-app/pull/2
- Official-repository verification workflow: https://github.com/DomTheDeveloper/test-expo-app/actions/runs/29366891772

## Specification and verification

- The definitions of `A005187`, `A046644`, and `A317940_f`, and the final theorem signature, were token-matched against `FormalConjectures/OEIS/Auto/317940_cd729cdd.lean` on `auto_oeis`.
- The exact proof was installed into a checkout of this repository and compiled under `FormalConjectures.Util.ProblemImports` with Lean 4.27.0.
- `#print axioms A317940_f_nonnegative` compiles successfully.
- A strict AXLE verification also returned no failed declarations, errors, or warnings.
- The proof contains no `sorry`, `admit`, or custom axiom.

Because the proof is substantially longer than the 25–50 line guideline in `CONTRIBUTING.md`, I am hosting it externally as recommended. I would appreciate maintainer guidance/review on marking the conjecture solved and attaching an appropriate `formal_proof using lean4` reference on the relevant branch.

## Proof idea

The prime-power Euler factor is normalized to

```text
B(z) = ∏_{r≥0} (1 + z^(2^r)/2).
```

The logarithmic derivative of its normalized square root has strictly positive coefficients. This gives an inductive positive recurrence for every square-root coefficient. After rescaling, these coefficients define a positive multiplicative arithmetic function whose Dirichlet square is `A046644`. Strong induction then identifies this function with the exact well-founded recursion `A317940_f`.

## Disclosure

The mathematical development and Lean formalization were produced with substantial assistance from OpenAI's ChatGPT. The final proof term is independently checked by the Lean kernel. Human review is requested.
