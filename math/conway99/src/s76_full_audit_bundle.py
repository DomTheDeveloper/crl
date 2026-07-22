#!/usr/bin/env python3
"""Aggregate proof-producing results for all 701 fixed ``s=76`` branches."""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from model import make_root_model
from verify import verify_reduced
from verify_matrix import verify_matrix


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
    parser.add_argument("--witnesses", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    profiles = json.loads(args.profiles.read_text())
    mapping = [int(value) for value in profiles["branch_profile_indices"]]
    assert len(mapping) == 701

    statuses = Counter()
    profile_statuses: dict[int, Counter[str]] = {
        profile: Counter() for profile in range(41)
    }
    records = []
    missing = []
    aggregate = hashlib.sha256(args.profiles.read_bytes())

    for orbit in range(701):
        path = args.results / f"orbit_{orbit:03d}.json"
        if not path.is_file():
            missing.append(orbit)
            continue
        record = json.loads(path.read_text())
        assert record["orbit"] == orbit
        assert record["profile_index"] == mapping[orbit]
        status = str(record["status"])
        statuses[status] += 1
        profile_statuses[mapping[orbit]][status] += 1

        if status == "VERIFIED_UNSAT":
            cnf_gz = args.proofs / f"orbit_{orbit:03d}.cnf.gz"
            proof_gz = args.proofs / f"orbit_{orbit:03d}.drup.gz"
            assert cnf_gz.is_file() and proof_gz.is_file()
            assert sha256(cnf_gz) == record["cnf_gzip_sha256"]
            assert sha256(proof_gz) == record["proof_gzip_sha256"]
        elif status == "VERIFIED_SAT":
            witness = args.witnesses / f"orbit_{orbit:03d}.json"
            assert witness.is_file()
            assert sha256(witness) == record["witness_sha256"]
            data = json.loads(witness.read_text())
            edges = [tuple(map(int, edge)) for edge in data["edges"]]
            verify_reduced(make_root_model(14), edges)
            verify_matrix(14, edges)
        records.append(record)
        aggregate.update(f"{orbit}\n".encode())
        aggregate.update(json.dumps(record, sort_keys=True, separators=(",", ":")).encode())

    complete = not missing and sum(statuses.values()) == 701
    verified_sat = statuses["VERIFIED_SAT"]
    verified_unsat = statuses["VERIFIED_UNSAT"]
    certified_s76_unsat = complete and verified_unsat == 701
    verified_conway_witness = verified_sat > 0

    manifest = {
        "PASS": True,
        "purpose": "aggregate exact fixed-transition search without promoting non-results",
        "expected_orbits": 701,
        "records_found": len(records),
        "missing_orbits": missing,
        "status_histogram": dict(sorted(statuses.items())),
        "profile_status_histogram": {
            str(profile): dict(sorted(counter.items()))
            for profile, counter in profile_statuses.items()
        },
        "complete_coverage": complete,
        "verified_sat_witnesses": verified_sat,
        "verified_unsat_orbits": verified_unsat,
        "certified_s76_unsat": certified_s76_unsat,
        "verified_conway_witness_found": verified_conway_witness,
        "profiles_sha256": sha256(args.profiles),
        "aggregate_sha256": aggregate.hexdigest(),
        "qualification": (
            "Only VERIFIED_UNSAT and VERIFIED_SAT count. TIMEOUT, ERROR, missing, "
            "UNKNOWN, and unchecked solver answers are explicit non-results."
        ),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
