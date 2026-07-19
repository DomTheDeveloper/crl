# Proposed arXiv metadata

## Title

The 2n-4 Bound for Checkerboard No-Three-in-Line Sets

## Author

Dominic A. Dabish

## Primary category

math.CO (Combinatorics)

## Secondary categories

- math.OC (Optimization and Control), optional
- cs.LO (Logic in Computer Science), optional because of the Lean formalization

## Abstract

Let D_mono(n) be the largest number of points that can be chosen from one parity class of the n x n integer grid with no three collinear. Prellberg proved the elementary bound D_mono(n) <= 2n-2 and proposed the sharper inequality D_mono(n) <= 2n-4 for n >= 6 as a boundary-forcing heuristic. We prove this inequality for every n >= 6. The proof is an explicit four-direction linear-programming dual certificate: quadratic weights on rows, columns, and the two diagonal families give constant coverage of every point in the chosen parity class, while their exact total cost lies strictly below the threshold for 2n-3 selected points. The thin 7 x 7 board is handled by a small integer certificate, and the two 6 x 6 colour classes by a finite kernel-checked Boolean verification. A complete Lean 4 formalization proves the exact all-n theorem and audits its axioms.

## Comments

Lean 4 formalization and exact finite checker included. This paper proves the finite upper bound only; it does not settle the exact values for all n or the conjectured all-slope asymptotic equality.

## Suggested journal

Electronic Journal of Combinatorics, after technical review and arXiv posting.
