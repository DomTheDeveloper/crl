# Certificate policy

This directory contains only regression certificates unless explicitly marked
otherwise. None of them proves existence or nonexistence of the Conway graph.

For a 99-vertex SAT witness, retain the reduced edge list and run both exact
verifiers. For UNSAT, retain the exact DIMACS file, proof trace, checker output,
solver/checker versions, and SHA-256 hashes. A global negative result also
requires a passing exhaustive coverage manifest.
