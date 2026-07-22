#!/usr/bin/env python3
"""Aggregate all 41 proof-producing position-sensitive S3 quotient results."""
from __future__ import annotations

import argparse
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--proofs", type=Path, required=True)
    parser.add_argument("--assignments", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    profiles = json.loads(args.profiles.read_text())
    assert profiles["PASS"] and len(profiles["profiles"]) == 41
    statuses = Counter()
    branch_statuses = Counter()
    records = []
    aggregate = hashlib.sha256(args.profiles.read_bytes())

    for profile in range(41):
        path = args.results / f"profile_{profile:02d}.json"
        assert path.is_file(), path
        record = json.loads(path.read_text())
        assert record["profile_index"] == profile
        assert record["profile"] == profiles["profiles"][profile]
        status = str(record["status"])
        statuses[status] += 1
        branch_statuses[status] += int(record["profile"]["branches"])
        if status == "VERIFIED_UNSAT":
            cnf = args.proofs / f"profile_{profile:02d}.cnf.gz"
            proof = args.proofs / f"profile_{profile:02d}.drup.gz"
            assert cnf.is_file() and proof.is_file()
            assert sha256(cnf) == record["cnf_gzip_sha256"]
            assert sha256(proof) == record["proof_gzip_sha256"]
        elif status == "VERIFIED_SAT":
            assignment = args.assignments / f"profile_{profile:02d}.json"
            assert assignment.is_file()
            assert sha256(assignment) == record["assignment_sha256"]
            payload = json.loads(assignment.read_text())
            assert payload["profile_index"] == profile
            assert payload["domains"] > 0
            assert payload["table_constraints"] > 0
        records.append(record)
        aggregate.update(f"{profile}\n".encode())
        aggregate.update(json.dumps(record, sort_keys=True, separators=(",", ":")).encode())

    assert sum(statuses.values()) == 41
    assert sum(branch_statuses.values()) == 701
    manifest = {
        "PASS": True,
        "purpose": "proof-producing position-sensitive S3 quotient classification",
        "canonical_core_types": 41,
        "completed_transition_orbits_covered": 701,
        "status_histogram": dict(sorted(statuses.items())),
        "branch_status_histogram": dict(sorted(branch_statuses.items())),
        "verified_unsat_profiles": statuses["VERIFIED_UNSAT"],
        "verified_sat_profiles": statuses["VERIFIED_SAT"],
        "complete_checked_classification": (
            statuses["VERIFIED_UNSAT"] + statuses["VERIFIED_SAT"] == 41
        ),
        "profiles_sha256": sha256(args.profiles),
        "aggregate_sha256": aggregate.hexdigest(),
        "proof_boundary": (
            "A VERIFIED_UNSAT quotient eliminates its core type. A VERIFIED_SAT quotient "
            "is only a necessary linear witness and must be lifted to S4/full branch data."
        ),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
