# Independent local DRAT replays for top mask 24

These exact subfamilies were emitted from the repository's
`n22_exact_core.build_double(24)` encoder with every left-boundary variable
fixed to the named mask. PySAT's CaDiCaL 1.9.5 backend generated textual DRAT
proofs. The official `marijnheule/drat-trim` executable, built from its upstream
source and SHA-256 checked, independently replayed each trace and returned
`s VERIFIED`.

| Left mask | Variables | Clauses | Proof lines | CNF SHA-256 | DRAT SHA-256 | Replay |
|---:|---:|---:|---:|---|---|---|
| 129 | 27,186 | 118,744 | 9,247 | `7f7203f9fb35eaa10fd5e700483e0533eaac0730a5edae7e6a73410a074470bf` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |
| 257 | 27,186 | 118,744 | 9,247 | `c5a6b7c6c458dafd770c8f3bea10d7cd65baee7b06267b531ab778f7e8a6dbe8` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |
| 513 | 27,186 | 118,744 | 9,247 | `698a8830269b962b39c4adc4855258ebf5e88a23afc8c07cc2deb8c40e399a9d` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |

The complete certificate bundle contains the DIMACS files, uncompressed DRAT
traces, JSON manifests, SHA-256 manifests, and replay transcripts. Its ZIP
SHA-256 is

```text
04fdfbcf235be9c07c3b656d15c8b6ff1487a71ef0179f78f55575db5b334430
```

These masks are members of the exact 46-mask disjoint partition proved by the
workflow's successful coverage job. They therefore permanently close three
specific branches of the canonical top-24 family.
