Subject: Proof of the checkerboard bound D_mono(n) <= 2n - 4

Dear Professor Prellberg,

I am writing about your preprint *No-three-in-line sets on the checkerboard grid* (arXiv:2605.09215). Your paper notes that boundary forcing suggests, but does not prove, the bound

D_mono(n) <= 2n - 4 for n >= 6.

I have obtained a proof of this bound using an explicit quadratic four-direction dual certificate. For odd and even side lengths, quadratic row, column, and diagonal weights give constant point coverage, and their exact objective is strictly below the threshold for 2n - 3 points. The thin 7 x 7 case has a small integer certificate, and the 6 x 6 case is verified by a finite Boolean argument.

The complete exact statement has also been formalized in Lean 4. The formal model uses the integer determinant and quantifies over all triples, so the theorem is the genuine all-slope NTIL upper bound; the four-direction capacities are derived as necessary conditions. The build and axiom audit reject sorry/admit, custom axioms, native_decide, and sorryAx.

I have attached a concise manuscript and reproducibility record. Before posting the result publicly, I would be grateful for your technical review, particularly of the novelty boundary and whether you know of any prior proof of the 2n - 4 inequality.

The result is deliberately scoped only to the finite upper bound. It does not claim exact values for every n or settle the conjectured asymptotic lower bound.

Best regards,

Dominic A. Dabish
Independent researcher
San Diego, California, USA
