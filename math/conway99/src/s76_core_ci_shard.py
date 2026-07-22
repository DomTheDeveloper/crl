#!/usr/bin/env python3
"""Solve one deterministic shard of the 41 canonical ``s = 76`` intact cores."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import s76_intact_core_cpsat as core_solver


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

    # The solver module imports the profile audit as a function.  Replace it
    # with the already checked preparation artifact so each worker does not
    # regenerate all 701 transition orbits.
    core_solver.core_profile_audit = lambda: report

    args.out.mkdir(parents=True, exist_ok=True)
    results_dir = args.out / "results"
    witnesses_dir = args.out / "witnesses"
    results_dir.mkdir(exist_ok=True)
    witnesses_dir.mkdir(exist_ok=True)

    profile_ids = [
        profile
        for profile in range(41)
        if profile % args.shard_count == args.shard_index
    ]
    records = []
    for position, profile in enumerate(profile_ids, 1):
        witness = witnesses_dir / f"profile_{profile:02d}.json"
        result = core_solver.solve_profile(
            profile,
            args.time_limit,
            args.workers,
            str(witness),
        )
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
    }
    atomic_json(args.out / f"shard_{args.shard_index:02d}.json", manifest)


if __name__ == "__main__":
    main()
