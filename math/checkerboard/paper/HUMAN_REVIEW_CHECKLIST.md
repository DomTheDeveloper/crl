# Human mathematical review checklist

This checklist is deliberately independent of the Lean build. Every item should be initialed by the author or an external mathematical reviewer before public submission.

## Definitions and scope

- [ ] Verify that `D_mono(n, epsilon)` is defined on one checkerboard parity class and that `D_mono(n)` takes the maximum of the two classes.
- [ ] Verify that the paper's NTIL condition is the genuine all-slope collinearity condition.
- [ ] Verify the implication from all-slope NTIL to capacity at most two on each row, column, sum diagonal, and difference diagonal.
- [ ] Verify that the theorem claims only the upper bound for `n >= 6`, not exact values or the asymptotic limit.

## Weighted certificate

- [ ] Check the weighted-incidence double count line by line.
- [ ] Check nonnegativity of every displayed row, column, and diagonal weight.
- [ ] Expand the master quadratic identity directly.
- [ ] Check the parity of the two diagonal indices on odd boards.
- [ ] Check the opposite shifted-difference parity on even boards.

## Odd boards

- [ ] Derive the odd axis sum.
- [ ] Derive the fat diagonal sum.
- [ ] Derive the thin diagonal sum.
- [ ] Recompute the fat total cost and strict gap for `m >= 3`.
- [ ] Recompute the thin total cost and strict gap for `m >= 4`.
- [ ] Check all 24 thin-colour points on the `7 x 7` board have coverage 3 or 4.
- [ ] Check the exceptional certificate cost is 32 and `32 < 3 * 11`.

## Even boards

- [ ] Derive the even axis sum.
- [ ] Derive the total selected diagonal sum.
- [ ] Recompute the even total cost.
- [ ] Recompute the strict gap for `m >= 4`.
- [ ] Confirm that at `m = 3` the normalized quadratic cost is `47/5`, so a finite argument is genuinely needed.

## The `6 x 6` base case

- [ ] Confirm each colour class has exactly 18 points.
- [ ] Confirm every feasible set of size at least nine contains a feasible nine-point subset.
- [ ] Independently run `python3 verify_small_cases.py`.
- [ ] Confirm the checksum: zero feasible nine-subsets and exactly 155 feasible eight-subsets in each parity class.
- [ ] Inspect the Lean transport from arbitrary monochromatic sets to 18 Boolean variables.
- [ ] Confirm `bv_decide` proves only the finite Boolean proposition and that the surrounding transport is kernel-checked Lean.

## Formal proof

- [ ] Run the pinned Lean build in a clean environment.
- [ ] Inspect `#print axioms Checkerboard.checkerboard_upper_all_n`.
- [ ] Confirm no `sorryAx`, custom project axiom, `sorry`, `admit`, or `native_decide` enters the theorem.
- [ ] Check the paper-to-Lean declaration table against the actual source.

## Literature and presentation

- [ ] Read Prellberg's full paper and check every description of its results.
- [ ] Verify all bibliography metadata against publisher or arXiv records.
- [ ] Repeat the novelty search immediately before posting.
- [ ] Read the final rendered PDF page by page.
- [ ] Confirm the affiliation, author-name form, email, ORCID, AI disclosure, and data-availability statement.
