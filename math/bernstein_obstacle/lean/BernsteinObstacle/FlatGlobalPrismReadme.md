# Flat global prism theorem

This branch removes the remaining global scalar lower-bound oracle from the explicit flat-interface Hilbert-VI theorem.

The proof combines:

1. the exact per-interface-square prism pair contribution `a^2 h^4 / 768`;
2. a codimension-one count `W / h <= #S`;
3. domination of the retained disjoint local energies by the global squared error;
4. the already certified Hilbert-space Falk transfer for the upper bound.

Terminal declarations:

- `flatInterface_prismPatch_lowerSq`
- `flatInterface_hilbertVI_sharp_from_prismPatch`
- `flatInterface_hilbertVI_sharp_of_finPatch`
