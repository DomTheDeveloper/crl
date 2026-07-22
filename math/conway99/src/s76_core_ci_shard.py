#!/usr/bin/env python3
"""Solve one deterministic shard of the 41 canonical ``s = 76`` intact cores."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import s76_intact_core_cpsat as core_solver
import s76_linear_quotient_cpsat as quotient_solver


def atomic_json(path: Path, data: dict[str, object]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--shard-index", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--time-limit", type=float, default=1200)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()

    report = json.loads(args.profiles.read_text())
    assert report["PASS"]
    assert report["completed_transition_orbits"] == 701
    assert report["S7_intact_core_orbits"] == 41
    assert len(report["profiles"]) == 41

    # Reuse the checked preparation artifact rather than regenerating all 701
    # transition orbits independently in every worker process.
    core_solver.core_profile_audit = lambda: report
    quotient_solver.core_profile_audit = lambda: report

    args.out.mkdir(parents=True, exist_ok=True)
    results_dir = args.out / "results"
    witnesses_dir = args.out / "witnesses"
    quotient_witnesses_dir = args.out / "quotient_witnesses"
    results_dir.mkdir(exist_ok=True)
    witnesses_dir.mkdir(exist_ok=True)
    quotient_witnesses_dir.mkdir(exist_ok=True)

    profile_ids = [
        profile
        for profile in range(41)
        if profile % args.shard_count == args.shard_index
    ]
    records = []
    for position, profile in enumerate(profile_ids, 1):
        quotient_witness = quotient_witnesses_dir / f"profile_{profile:02d}.json"
        quotient_result = quotient_solver.solve_profile(
            profile,
            min(args.time_limit, 600),
            args.workers,
            str(quotient_witness),
        )
        if quotient_result["status"] not in ("OPTIMAL", "FEASIBLE") and quotient_witness.exists():
            quotient_witness.unlink()

        witness = witnesses_dir / f"profile_{profile:02d}.json"
        result = core_solver.solve_profile(
            profile,
            args.time_limit,
            args.workers,
            str(witness),
        )
        result["linear_quotient"] = quotient_result
        result["shard_index"] = args.shard_index
        result["shard_count"] = args.shard_count
        result["shard_position"] = position
        result["shard_profiles"] = len(profile_ids)
        if result["status"] not in ("OPTIMAL", "FEASIBLE") and witness.exists():
            witness.unlink()
        atomic_json(results_dir / f"profile_{profile:02d}.json", result)
        records.append(result)
        print("RESULT_JSON " + json.dumps(result, sort_keys=True), flush=True)

    manifest = {
        "PASS": True,
        "shard_index": args.shard_index,
        "shard_count": args.shard_count,
        "profile_ids": profile_ids,
        "profiles_completed": len(records),
        "status_histogram": {
            status: sum(record["status"] == status for record in records)
            for status in sorted({record["status"] for record in records})
        },
        "quotient_status_histogram": {
            status: sum(record["linear_quotient"]["status"] == status for record in records)
            for status in sorted(
                {record["linear_quotient"]["status"] for record in records}
            )
        },
    }
    atomic_json(args.out / f"shard_{args.shard_index:02d}.json", manifest)


if __name__ == "__main__":
    main()
