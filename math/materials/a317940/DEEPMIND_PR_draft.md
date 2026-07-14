## Summary

This replaces the `sorry` in `A317940_f_nonnegative` with a complete proof and adds the supporting lemmas needed to prove the stronger result that `A317940_f n > 0` for every `n > 0`.

## Mathematical idea

The proof reduces the multiplicative Dirichlet-square-root problem to prime powers. After normalizing

\[
2^{A005187(e)} = 4^e 2^{-s_2(e)},
\]

the local target series is

\[
B(z)=\sum_{e\ge0}2^{-s_2(e)}z^e
    =\prod_{r\ge0}\left(1+\frac{z^{2^r}}2\right).
\]

The formal square root `A` is shown to have strictly positive coefficients. The Lean development uses a coefficientwise logarithmic-derivative recurrence, avoiding analytic convergence. Rescaling provides positive prime-power coefficients whose local convolution is exactly `2 ^ A005187 e`. These coefficients are lifted to a multiplicative arithmetic function `rootAF`; the proof establishes `rootAF * rootAF = A046644` and then identifies `rootAF` with the existing well-founded recursive definition `A317940_f` by strong induction.

## Stronger result

The submitted proof establishes strict positivity internally:

```lean
A317940Verified.rootAF_pos : 0 < n → 0 < rootAF n
A317940Verified.A317940_f_eq_rootAF : A317940_f n = rootAF n
```

and concludes the original theorem:

```lean
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) :
    A317940_f n ≥ 0
```

## Specification fidelity

The definitions of `A005187`, `A046644`, and `A317940_f`, and the final theorem signature, are unchanged. An automated token-level integrity check compares them with the current `auto_oeis` source.

## Validation

- strict Lean 4.27 verification: passed;
- no `sorry`, `admit`, or custom axioms in the proof;
- exact source file compiled under `FormalConjectures.Util.ProblemImports`;
- full `lake --wfail build`: passed;
- `#print axioms A317940_f_nonnegative`: attached in the CI artifact;
- exact rational computations were separately cross-checked with Python, GMP C++, Java/BigInteger, and SymPy.

## AI assistance disclosure

The proof strategy, Lean formalization, and debugging were developed with substantial assistance from OpenAI's ChatGPT. The submitted Lean term is independently checked by the Lean kernel. Human review of the mathematical exposition and source maintainability is requested.
