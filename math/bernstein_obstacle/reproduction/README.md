# One-command Bernstein obstacle reproduction

From this directory:

```bash
python -m pip install -r requirements.txt
python reproduce_all.py --output-dir reproduction-output
```

The command regenerates the proof stress tests, the custom curved quadratic
Bernstein--Bézier Hertz/Signorini benchmark, and the independent scikit-fem
assembly. It fails unless all certificate, KKT, geometry, force-balance, Hertz,
and cross-framework tolerances pass.

The final machine-readable verdict is
`reproduction-output/REPRODUCTION_PASS.json`.

## GitHub Actions

`.github/workflows/bernstein-obstacle-reproduction.yml` reconstructs the pinned
source archive from `source/part_*.b64`, checks SHA-256
`958a0ed22a9a6e2ad838b42345a2a2ce2573268032733f35d5d6343cf28aa00c`, installs
the pinned dependencies, runs both FEM implementations, and uploads the raw
reproduction outputs.

This reproduces computational evidence. It does not independently certify the
multidimensional analytical proof or count as an external third-party report.
