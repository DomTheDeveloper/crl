#!/usr/bin/env python3
"""Aggregate all 41 certified ``s = 76`` parity/conjugacy projections."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def decompressed_sha(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    lines = 0
    with gzip.open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
            lines += block.count(b"\n")
    return digest.hexdigest(), lines


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--proofs", type=Path, required=True)
    parser.add_argument("--assignments", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    profile_report = json.loads(args.profiles.read_text())
    assert profile_report["PASS"] and len(profile_report["profiles"]) == 41
    profiles_sha = sha256(args.profiles)

    statuses = Counter()
    branch_statuses = Counter()
    proof_hashes = set()
    cnf_hashes = set()
    records = []
    for profile in range(41):
        result_path = args.results / f"profile_{profile:02d}.json"
        assert result_path.is_file(), result_path
        record = json.loads(result_path.read_text())
        assert record["profile_index"] == profile
        assert record["profile"] == profile_report["profiles"][profile]
        assert record["profiles_sha256"] == profiles_sha
        assert record["cnf_sha256"] not in cnf_hashes
        cnf_hashes.add(record["cnf_sha256"])
        status = record["status"]
        statuses[status] += 1
        branch_statuses[status] += int(record["profile"]["branches"])

        if status == "VERIFIED_UNSAT":
            proof = args.proofs / f"profile_{profile:02d}.drup.gz"
            assert proof.is_file()
            assert sha256(proof) == record["proof_gzip_sha256"]
            raw_sha, lines = decompressed_sha(proof)
            assert raw_sha == record["proof_sha256"]
            assert lines == record["proof_lines"]
            assert record["proof_sha256"] not in proof_hashes
            proof_hashes.add(record["proof_sha256"])
            assert "s VERIFIED" in record["checker_stdout"]
        else:
            assert status == "SAT_VERIFIED_NECESSARY_ASSIGNMENT"
            assignment = args.assignments / f"profile_{profile:02d}.json"
            assert assignment.is_file()
            assert sha256(assignment) == record["assignment_sha256"]
        records.append(record)

    assert sum(statuses.values()) == 41
    assert sum(branch_statuses.values()) == 701
    aggregate = hashlib.sha256()
    aggregate.update(args.profiles.read_bytes())
    for profile, record in enumerate(records):
        aggregate.update(f"{profile}\n".encode())
        aggregate.update(record["cnf_sha256"].encode())
        aggregate.update(record["status"].encode())
        if record["status"] == "VERIFIED_UNSAT":
            aggregate.update(record["proof_sha256"].encode())
        else:
            aggregate.update(record["assignment_sha256"].encode())

    eliminated_branches = branch_statuses["VERIFIED_UNSAT"]
    manifest = {
        "PASS": True,
        "projection": "S4 edge parity plus triangle conjugacy class",
        "canonical_core_types": 41,
        "completed_transition_orbits_covered": 701,
        "status_histogram": dict(sorted(statuses.items())),
        "branch_status_histogram": dict(sorted(branch_statuses.items())),
        "certified_eliminated_transition_orbits": eliminated_branches,
        "surviving_transition_orbits": 701 - eliminated_branches,
        "distinct_cnf_hashes": len(cnf_hashes),
        "distinct_unsat_proof_hashes": len(proof_hashes),
        "profiles_sha256": profiles_sha,
        "aggregate_sha256": aggregate.hexdigest(),
        "logical_boundary": (
            "A VERIFIED_UNSAT profile is rigorously eliminated because the CNF "
            "encodes necessary conditions. A SAT profile only survives this "
            "projection and remains to be checked by stronger core/full models."
        ),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
