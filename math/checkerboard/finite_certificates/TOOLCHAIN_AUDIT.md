# Proof-toolchain audit

The certificate workflows pin every external solver and checker by full Git
commit. No floating tag or default branch is used.

## CaDiCaL

Commit:

```text
7b99c07f0bcab5824a5a3ce62c7066554017f641
```

The pinned README states the command-line contract as:

```text
cadical [ dimacs [ proof ] ]
```

The workflow therefore passes the deterministic DIMACS instance as the first
positional argument and the DRAT output path as the second. The solver result is
accepted only when the process finishes before the external timeout and its log
contains `s UNSATISFIABLE`.

## Kissat

Commit:

```text
8af8e56f174b778aef3aa45af9f739b2a5f492c2
```

Kissat independently solves the same byte-identical DIMACS input. It is not
used to generate the checked proof artifact. Its result is accepted only when
the process finishes and its log contains `s UNSATISFIABLE`.

## drat-trim and lrat-check

Commit:

```text
2e3b2dc0ecf938addbd779d42877b6ed69d9a985
```

Pinned source identities:

```text
drat-trim.c  git-blob cf8a676ffcc7ef5a47124bbafc9b680a2df333e0
lrat-check.c  git-blob 8fe998a14efa91daccc85404ceb5e871a86d99e4
Makefile      git-blob 9c3d881d55ef4dae9a7136f710d715b1949d5f14
```

At this commit:

- `drat-trim INPUT PROOF -L OUTPUT` is explicitly implemented and documented as
  writing the core lemmas in LRAT format;
- `drat-trim` returns zero only after successful verification;
- the Makefile builds both `drat-trim` and `lrat-check`;
- `lrat-check CNF LRAT` returns zero only after deriving and validating the
  empty clause and prints `c VERIFIED`.

The workflow uses `set -o pipefail`, checks each exit status through the shell,
requires the LRAT file to be nonempty, and stores SHA-256 hashes before
compression and after compression.

## Result policy

The following are all **no result**:

- external timeout exit code 124;
- solver `UNKNOWN` or resource-limit status;
- missing or malformed status line;
- empty proof output;
- nonzero `drat-trim` or `lrat-check` exit;
- a proof-checker log that does not show successful verification.

Only a completed solver result plus a successfully checked proof artifact can
certify an upper-bound instance.
