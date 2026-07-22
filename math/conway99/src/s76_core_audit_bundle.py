#!/usr/bin/env python3
"""Aggregate complete discovery results for the 41 canonical ``s = 76`` cores."""
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
    parser.add_argument("--witnesses", type=Path, required=True)
    parser.add_argument("--quotient-witnesses", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    profiles = json.loads(args.profiles.read_text())
    assert profiles["PASS"]
    assert profiles["completed_transition_orbits"] == 701
    assert profiles["S7_intact_core_orbits"] == 41

    records = []
    statuses = Counter()
    quotient_statuses = Counter()
    covered_branches = Counter()
    quotient_covered_branches = Counter()
    for profile in range(41):
        path = args.results / f"profile_{profile:02d}.json"
        assert path.is_file(), path
        record = json.loads(path.read_text())
        assert record["profile_index"] == profile
        assert record["profile"] == profiles["profiles"][profile]
        status = record["status"]
        statuses[status] += 1
        covered_branches[status] += int(record["profile"]["branches"])
        if status in ("OPTIMAL", "FEASIBLE"):
            assert record.get("verified_core") is True
            witness = args.witnesses / f"profile_{profile:02d}.json"
            assert witness.is_file()
            record["witness_sha256"] = sha256(witness)

        quotient = record["linear_quotient"]
        assert quotient["profile_index"] == profile
        assert quotient["profile"] == profiles["profiles"][profile]
        quotient_status = quotient["status"]
        quotient_statuses[quotient_status] += 1
        quotient_covered_branches[quotient_status] += int(record["profile"]["branches"])
        if quotient_status in ("OPTIMAL", "FEASIBLE"):
            assert quotient.get("verified_quotient") is True
            quotient_witness = args.quotient_witnesses / f"profile_{profile:02d}.json"
            assert quotient_witness.is_file()
            quotient["witness_sha256"] = sha256(quotient_witness)
        records.append(record)

    assert sum(statuses.values()) == 41
    assert sum(quotient_statuses.values()) == 41
    assert sum(covered_branches.values()) == 701
    assert sum(quotient_covered_branches.values()) == 701
    aggregate = hashlib.sha256()
    aggregate.update(args.profiles.read_bytes())
    for profile, record in enumerate(records):
        aggregate.update(f"{profile}\n".encode())
        aggregate.update(json.dumps(record, sort_keys=True, separators=(",", ":")).encode())

    manifest = {
        "PASS": True,
        "purpose": "discovery-only position-sensitive quotient and intact-core classification",
        "canonical_core_types": 41,
        "completed_transition_orbits_covered": 701,
        "quotient_status_histogram": dict(sorted(quotient_statuses.items())),
        "quotient_branch_status_histogram": dict(sorted(quotient_covered_branches.items())),
        "status_histogram": dict(sorted(statuses.items())),
        "branch_status_histogram": dict(sorted(covered_branches.items())),
        "profiles_sha256": sha256(args.profiles),
        "aggregate_sha256": aggregate.hexdigest(),
        "proof_boundary": (
            "INFEASIBLE in either CP-SAT layer is discovery evidence only. Each eliminated "
            "core type must be converted to an independently checked SAT/XOR certificate."
        ),
        "next_step": (
            "Mine compact certificates from quotient/core failures and run the exact full "
            "fixed-transition SAT campaign on every branch not independently certified away."
        ),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
