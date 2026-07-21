# Independent local DRAT replays and direct corner reductions for top mask 24

## Direct corner lemma

The designated top and left boundaries share the point `(0,0)`, represented by
bit 0 in both 11-bit boundary masks. Every exact top/left subfamily fixes this
same Boolean point variable twice, once from each mask. Consequently the two
bit-0 values must agree.

The canonical top mask `24` has bit 0 equal to zero. Hence every odd left mask
has bit 0 equal to one and is impossible immediately: its CNF contains the
complementary unit clauses for `(0,0)`.

Among the 46 canonical left masks `left >= 24`, the six directly contradictory
odd masks are

```text
33, 65, 129, 257, 513, 1025.
```

Thus only 40 even masks require nontrivial SAT proofs.

## Independently replayed local certificates

The exact subfamilies below were emitted from the repository's
`n22_exact_core.build_double(24)` encoder. PySAT's CaDiCaL 1.9.5 backend
generated textual DRAT proofs. The official `marijnheule/drat-trim` executable,
built from upstream source and SHA-256 checked, independently replayed each
listed trace and returned `s VERIFIED`.

| Left mask | Variables | Clauses | Proof lines | CNF SHA-256 | DRAT SHA-256 | Replay |
|---:|---:|---:|---:|---|---|---|
| 129 | 27,186 | 118,744 | 9,247 | `7f7203f9fb35eaa10fd5e700483e0533eaac0730a5edae7e6a73410a074470bf` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |
| 257 | 27,186 | 118,744 | 9,247 | `c5a6b7c6c458dafd770c8f3bea10d7cd65baee7b06267b531ab778f7e8a6dbe8` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |
| 513 | 27,186 | 118,744 | 9,247 | `698a8830269b962b39c4adc4855258ebf5e88a23afc8c07cc2deb8c40e399a9d` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |
| 1025 | 27,186 | 118,744 | 9,247 | `f9269e3fa58da91d0f19e5ab88de11223569be8e2fd477febbbed0168f77c004` | `a119a167b92e5a2f0d58233302412c7eb0f2d9368f17a939b7606800a15b5f0c` | `s VERIFIED` |

The identical short proof hashes reflect the same complementary-unit
contradiction; the CNF hashes differ because the remaining left-boundary units
differ.

The earlier certificate bundle for masks 129, 257, and 513 has ZIP SHA-256

```text
04fdfbcf235be9c07c3b656d15c8b6ff1487a71ef0179f78f55575db5b334430
```

All masks listed here belong to the exact disjoint partition proved by the
workflow's successful coverage job.
