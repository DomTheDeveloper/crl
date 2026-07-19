Dear Editors,

Please consider the manuscript **The 2n-4 Bound for Checkerboard No-Three-in-Line Sets** for publication in *The Electronic Journal of Combinatorics*.

The paper proves a finite extremal bound recorded as conjectural in Thomas Prellberg's 2026 paper on the checkerboard-restricted no-three-in-line problem. For every `n >= 6`, every no-three-in-line subset of either checkerboard parity class of the `n x n` integer grid has at most `2n - 4` points.

The proof is explicit and self-contained. It constructs quadratic nonnegative weights on rows, columns, and the two slope-`+-1` diagonal families. These weights give constant coverage of every point in the selected parity class, while their exact total cost rules out `2n - 3` points. The thin `7 x 7` board is handled by a small integer line cover, and the two `6 x 6` classes by an exact finite Boolean verification.

A complete Lean 4 formalization accompanies the paper. The formal statement uses the integer determinant and quantifies over all triples of distinct selected points; the four-direction capacities are derived from the genuine all-slope no-three-in-line hypothesis. The repository also contains independent standard-library checkers for the finite exceptions and exact-arithmetic cross-checks of the quadratic formulas.

OpenAI's ChatGPT assisted with proof exploration, Lean formalization, code generation, and manuscript editing. I have checked the mathematical argument and remain fully responsible for the submission. The manuscript includes an explicit AI-assistance disclosure and enough detail for a human referee to verify every argument, in accordance with the journal's policy.

The manuscript has not been submitted elsewhere. Before submission, I will confirm that this statement remains true and provide the final affiliation, email address, and archival code reference. To the best of my knowledge, this is the first proof of the proposed `2n - 4` bound; the priority statement is qualified in the paper because unindexed or simultaneous work may exist.

Sincerely,

Dominic A. Dabish
[final affiliation]
[submission email]
