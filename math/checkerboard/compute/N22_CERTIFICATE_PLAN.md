# Exact completion and certificate plan for `D_mono(22)`

## Mathematical reduction

The rational four-direction dual has denominator `187`, objective numerator `6470`, and therefore exact slack

```text
6470 - 34 * 187 = 112.
```

Each of the four outer boundary lines has dual weight `63` and capacity two.

- An empty outer boundary contributes `2 * 63 = 126 > 112`, so every outer boundary is nonempty.
- Two singleton outer boundaries contribute at least `63 + 63 = 126 > 112`, so at most one outer boundary is singleton.

Consequently every hypothetical 34-point configuration lies in exactly one of two regimes:

1. one singleton outer boundary, moved to the top by dihedral symmetry, with 11 possible top cells;
2. all four outer boundaries contain exactly two points.

In the all-double regime, dihedral symmetry makes the top boundary mask the least of the four two-point masks. Corner consistency determines the parity restrictions used by the exact sharder. The residual stabilizer when one or more additional boundary masks equal the top mask gives the terminal `rr` ordering conditions in `n22_double_shard_reduced.py`.

## Exact CNF

The current exact model contains:

- 242 checkerboard-compatible point variables;
- exact cardinality 34;
- all 2,455 all-slope line capacities;
- the exact 112-unit rational dual-slack identity;
- exact boundary cardinalities and canonical mask restrictions.

Long geometric lines use sequential at-most-two counters rather than expanding every forbidden triple. This is logically equivalent and reduces the production top-family model to roughly 99,700 clauses.

For every weighted line with `2w > 112`, emptiness is impossible. If two such lines were singleton, their slack would exceed 112, so at most one corresponding `low` flag is true. This sound strengthening is included in `n22_exact_core.py`.

## Decision phase

The optimized decision matrix uses CaDiCaL 1.9.5 and emits JSONL manifests. A result counts only when:

- the job terminates normally;
- no SAT/witness row occurs;
- the shard has one closed `UNSAT` summary;
- the independent auditor confirms complete, nonoverlapping coverage.

Timeouts, cancellations, `UNKNOWN`, missing artifacts, malformed summaries, and incomplete branch sets are no result.

The sharder performs deterministic boundary-only checks, bounded direct parent solves, exact terminal solves, and learned parent re-probing. A `left_refined` or `rb_refined` row means the complete parent formula was proved UNSAT after child-generated globally valid learned clauses; the independent coverage auditor treats it as a complete parent closure.

## Certificate phase

The decision manifests define a disjoint proof tree. Each solver-derived closed node is rerun as an ordinary DIMACS formula with the boundary assumptions appended as unit clauses.

For every such node:

1. CaDiCaL emits a DRAT proof.
2. Pinned upstream `drat-trim` independently checks the DRAT proof.
3. `drat-trim` translates the proof to LRAT.
4. Pinned upstream `lrat-check` independently checks the LRAT proof.
5. SHA-256 hashes are recorded for the CNF, DRAT, LRAT, logs, and metadata.

Boundary-only closures carry small explicit certificates:

- the three selected collinear boundary point IDs, or
- the selected boundary point excesses whose sum is greater than 112.

The final global checker must verify:

- the singleton/all-double regime partition;
- all symmetry and corner-parity partitions;
- every shard assignment and terminal-mask partition;
- every explicit boundary certificate;
- every LRAT leaf proof;
- zero witnesses and zero unresolved cases.

## Completion criterion

Only the following permits the exact conclusion

```text
D_mono(22) = 33.
```

- all 11 singleton cases are covered and certified UNSAT;
- all 55 canonical all-double top families are covered and certified UNSAT;
- the global independent audit passes;
- the known 33-point construction passes the independent determinant checker.

A single independently verified 34-point coordinate set instead proves `D_mono(22) = 34` immediately.
