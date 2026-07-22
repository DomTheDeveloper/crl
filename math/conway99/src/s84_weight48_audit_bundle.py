#!/usr/bin/env python3
"""Aggregate and audit all 90 weight-48 translation-lift certificates."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

from s84_weight48_translation_sat import load_representatives


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def decompressed_audit(path: Path) -> tuple[str, int, int]:
    digest = hashlib.sha256()
    line_count = 0
    byte_count = 0
    with gzip.open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
            byte_count += len(block)
            line_count += block.count(b"\n")
    return digest.hexdigest(), line_count, byte_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--representatives", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--proofs", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    data = load_representatives(args.representatives)
    representatives_sha = sha256(args.representatives)
    records = []
    proof_hashes = set()
    cnf_hashes = set()
    total_lines = 0
    total_compressed_bytes = 0
    total_uncompressed_bytes = 0
    variable_histogram = Counter()
    clause_histogram = Counter()

    result_files = sorted(args.results.glob("orbit_*.json"))
    proof_files = sorted(args.proofs.glob("orbit_*.drup.gz"))
    assert len(result_files) == len(proof_files) == 90

    for orbit in range(90):
        result_path = args.results / f"orbit_{orbit:02d}.json"
        proof_path = args.proofs / f"orbit_{orbit:02d}.drup.gz"
        assert result_path.is_file(), result_path
        assert proof_path.is_file(), proof_path
        record = json.loads(result_path.read_text())
        assert record["orbit"] == orbit
        assert record["status"] == "VERIFIED_UNSAT"
        assert record["representatives_sha256"] == representatives_sha
        assert record["proof_gzip_sha256"] == sha256(proof_path)
        assert "s VERIFIED" in record["checker_stdout"]

        decompressed_sha, lines, uncompressed_bytes = decompressed_audit(proof_path)
        assert decompressed_sha == record["proof_sha256"]
        assert lines == record["proof_lines"]
        assert record["proof_gzip_bytes"] == proof_path.stat().st_size
        assert record["proof_sha256"] not in proof_hashes
        assert record["cnf_sha256"] not in cnf_hashes
        proof_hashes.add(record["proof_sha256"])
        cnf_hashes.add(record["cnf_sha256"])

        total_lines += lines
        total_compressed_bytes += proof_path.stat().st_size
        total_uncompressed_bytes += uncompressed_bytes
        variable_histogram[record["variables"]] += 1
        clause_histogram[record["clauses"]] += 1
        records.append(record)

    aggregate = hashlib.sha256()
    aggregate.update(args.representatives.read_bytes())
    for orbit, record in enumerate(records):
        aggregate.update(f"{orbit}\n".encode())
        aggregate.update(record["cnf_sha256"].encode())
        aggregate.update(record["proof_sha256"].encode())
        aggregate.update(record["proof_gzip_sha256"].encode())

    manifest = {
        "PASS": True,
        "branch": "s=84, odd-holonomy support weight 48",
        "support_orbit_size": data["S7_support_orbit_size"],
        "gauge_fixed_quotient_connections": data["gauge_fixed_quotient_connections"],
        "frame_solutions_per_quotient": data["frame_solutions_per_quotient"],
        "unique_physical_linear_configurations": data["unique_physical_linear_configurations"],
        "physical_linear_orbits": data["physical_linear_orbits"],
        "orbit_size_histogram": data["orbit_size_histogram"],
        "verified_unsat_orbits": len(records),
        "representatives_sha256": representatives_sha,
        "distinct_cnf_hashes": len(cnf_hashes),
        "distinct_proof_hashes": len(proof_hashes),
        "total_proof_lines": total_lines,
        "total_proof_gzip_bytes": total_compressed_bytes,
        "total_proof_uncompressed_bytes": total_uncompressed_bytes,
        "variable_histogram": {
            str(value): count for value, count in sorted(variable_histogram.items())
        },
        "clause_histogram": {
            str(value): count for value, count in sorted(clause_histogram.items())
        },
        "aggregate_sha256": aggregate.hexdigest(),
        "consequence": (
            "Every physical-linear orbit in the weight-48 s=84 sector has an "
            "independently replayed UNSAT proof. Therefore any surviving s=84 "
            "Conway graph must have odd holonomy on exactly 56 triangles."
        ),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
