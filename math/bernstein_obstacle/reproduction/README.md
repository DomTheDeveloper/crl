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

This reproduces computational evidence. It does not independently certify the
multidimensional analytical proof.
