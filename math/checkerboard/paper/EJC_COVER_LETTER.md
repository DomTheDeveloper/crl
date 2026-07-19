Dear Editors,

Please consider the manuscript **The 2n-4 Bound for Checkerboard No-Three-in-Line Sets** for publication in *The Electronic Journal of Combinatorics*.

The paper proves a finite extremal bound proposed heuristically in Thomas Prellberg's 2026 paper on the checkerboard-restricted no-three-in-line problem. For every `n >= 6`, every no-three-in-line subset of either checkerboard parity class of the `n x n` integer grid has at most `2n - 4` points.

The proof is short and explicit. It constructs quadratic nonnegative weights on rows, columns, and the two slope-`+-1` diagonal families. These weights give constant coverage of every point in the selected parity class, while their exact total cost rules out `2n - 3` points. Two finite exceptions are handled by an integer certificate at the thin `7 x 7` board and an exact Boolean verification at `6 x 6`.

A complete Lean 4 formalization accompanies the paper. The formal statement uses the integer determinant and quantifies over all triples of distinct selected points; the four-direction capacities are derived from the genuine all-slope no-three-in-line hypothesis. The repository also contains independent standard-library checkers for the finite exceptions and exact-arithmetic cross-checks of the quadratic formulas.

OpenAI's ChatGPT assisted with proof exploration, Lean formalization, code generation, and manuscript editing. I have checked the mathematical argument and remain fully responsible for the submission. The manuscript includes an explicit AI-assistance disclosure and enough detail for a human referee to verify every argument, in accordance with the journal's policy.

The manuscript has not been published or submitted elsewhere. A preprint may be posted on arXiv after technical review. To the best of my knowledge, this is the first proof of the proposed `2n - 4` bound; I have also contacted Professor Prellberg for technical and priority review.

Sincerely,

Dominic A. Dabish
Independent researcher
San Diego, California, USA
