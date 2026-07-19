# Prior-art and novelty audit

Date: 18 July 2026

## Result audited

For every integer `n >= 6` and either checkerboard parity class, every no-three-in-line subset of the `n x n` integer grid has at most `2n - 4` points.

## Primary source

Thomas Prellberg's May 2026 preprint *No-three-in-line sets on the checkerboard grid* introduces the fixed-parity problem, proves the elementary `2n - 2` bound, and develops the four-direction linear-programming relaxation. In its discussion of boundary forcing, it states that the mechanism suggests, but does not prove, the sharper `2n - 4` inequality for `n >= 6`.

Reference:

- Thomas Prellberg, *No-three-in-line sets on the checkerboard grid*, arXiv:2605.09215 (2026).

## Search performed

The audit searched the exact theorem, its notation, the phrase `2n-4`, checkerboard no-three-in-line, monochromatic no-three-in-line, and four-direction checkerboard line covers across:

- arXiv and general scholarly web search;
- Google-indexed preprints and papers;
- GitHub code and pull-request search;
- references and terminology in Prellberg's paper;
- recent no-three-in-line literature through July 2026.

The search was repeated after completion of the publication manuscript on 18 July 2026. No earlier public proof of the all-`n` inequality was located. The new proof is structurally different from the boundary-deficit sketch: it uses an explicit quadratic dual line cover with constant point coverage, plus exact finite exceptions at `n=6` and the thin `n=7` colour.

## Qualification

This establishes a strong, good-faith novelty basis, not an absolute priority guarantee. Unindexed manuscripts, private communications, or simultaneous independent work may exist. The recommended publication wording is therefore:

> To the author's knowledge, this is the first proof of the bound proposed in Prellberg's paper.

Before public submission, repeat the search and obtain independent human review. Any technical-review outreach remains optional and requires explicit author approval.

## Scope boundary

The result proves only the finite upper bound. It does not determine `D_mono(n)` exactly for every `n` and does not prove the conjectured all-slope asymptotic lower bound or limit equality.
