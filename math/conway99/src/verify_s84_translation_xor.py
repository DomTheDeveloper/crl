#!/usr/bin/env python3
"""Replay the stored ``s = 84`` translation XOR certificate."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from s84_translation_parity_audit import build_linear_system, connection


def binary_rank(rows, columns):
    work = rows[:]
    rank = 0
    for column in range(columns):
        pivot = next(
            (i for i in range(rank, len(work)) if (work[i] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for i in range(rank + 1, len(work)):
            if (work[i] >> column) & 1:
                work[i] ^= work[rank]
        rank += 1
    return rank


def verify(path=None):
    root = Path(__file__).resolve().parents[1]
    certificate_path = (
        Path(path)
        if path is not None
        else root / "certificates" / "S84_TRANSLATION_XOR.json"
    )
    certificate = json.loads(certificate_path.read_text())

    data, _, holonomy = connection()
    equations, metadata = build_linear_system(data, holonomy)
    identifiers = [int(value) for value in certificate["certificate_ids"]]
    assert certificate["variables"] == 210
    assert certificate["equations_total"] == len(equations) == 546
    assert len(identifiers) == 54
    assert len(set(identifiers)) == 54
    assert min(identifiers) >= 0 and max(identifiers) < len(equations)

    combined = 0
    for identifier in identifiers:
        combined ^= equations[identifier]
    assert combined == 1 << 210

    coefficient_rows = [row & ((1 << 210) - 1) for row in equations]
    coefficient_rank = binary_rank(coefficient_rows, 210)
    augmented_rank = binary_rank(equations, 211)
    assert coefficient_rank == certificate["coefficient_rank"] == 169
    assert augmented_rank == certificate["augmented_rank"] == 170

    descriptions = [metadata[identifier] for identifier in identifiers]
    payload = json.dumps(
        {"ids": identifiers, "descriptions": descriptions},
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    digest = hashlib.sha256(payload).hexdigest()
    assert digest == certificate["certificate_sha256"]

    return {
        "PASS": True,
        "certificate": str(certificate_path),
        "selected_rows": len(identifiers),
        "coefficient_rank": coefficient_rank,
        "augmented_rank": augmented_rank,
        "certificate_sha256": digest,
        "contradiction": "0 = 1 over F2",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
