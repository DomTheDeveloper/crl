#!/usr/bin/env python3
"""Solve and independently replay one shard of ``s = 76`` parity-class CNFs."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

from pysat.solvers import Solver

from s76_parity_class_sat import Model, write_dimacs


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_json(path: Path, data: dict[str, object]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--shard-index", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--solver", default="glucose4")
    args = parser.parse_args()

    report = json.loads(args.profiles.read_text())
    assert report["PASS"] and len(report["profiles"]) == 41
    profile_ids = [
        profile for profile in range(41)
        if profile % args.shard_count == args.shard_index
    ]

    args.out.mkdir(parents=True, exist_ok=True)
    results = args.out / "parity_results"
    proofs = args.out / "parity_proofs"
    assignments = args.out / "parity_assignments"
    work = args.out / "parity_work"
    for directory in (results, proofs, assignments, work):
        directory.mkdir(exist_ok=True)

    profiles_sha = sha256(args.profiles)
    records = []
    for profile in profile_ids:
        data = report["profiles"][profile]
        model = Model(data)
        cnf = work / f"profile_{profile:02d}.cnf"
        proof = work / f"profile_{profile:02d}.drup"
        write_dimacs(cnf, model.variables, model.clauses)
        cnf_sha = sha256(cnf)

        with Solver(
            name=args.solver,
            bootstrap_with=model.clauses,
            with_proof=True,
        ) as solver:
            satisfiable = solver.solve()
            if satisfiable:
                positive = {literal for literal in solver.get_model() if literal > 0}
                verified = model.verify_assignment(positive)
                assignment = assignments / f"profile_{profile:02d}.json"
                assignment.write_text(
                    json.dumps(
                        {
                            "profile_index": profile,
                            "profile": data,
                            "positive_literals": sorted(positive),
                            **verified,
                        },
                        indent=2,
                        sort_keys=True,
                    )
                    + "\n"
                )
                record = {
                    "profile_index": profile,
                    "profile": data,
                    "status": "SAT_VERIFIED_NECESSARY_ASSIGNMENT",
                    "variables": model.variables,
                    "clauses": len(model.clauses),
                    "cnf_sha256": cnf_sha,
                    "profiles_sha256": profiles_sha,
                    "assignment_sha256": sha256(assignment),
                    **verified,
                }
            else:
                trace = solver.get_proof()
                if not trace:
                    raise RuntimeError(f"UNSAT profile {profile} returned no proof")
                proof.write_text("\n".join(trace) + "\n")
                proof_sha = sha256(proof)
                checked = subprocess.run(
                    [str(args.checker), str(cnf), str(proof)],
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=900,
                )
                if checked.returncode or "s VERIFIED" not in checked.stdout:
                    raise RuntimeError(
                        f"proof replay failed for s76 parity profile {profile}: "
                        f"{checked.stdout} {checked.stderr}"
                    )
                compressed = proofs / f"profile_{profile:02d}.drup.gz"
                with proof.open("rb") as source, gzip.open(compressed, "wb", compresslevel=6) as target:
                    while True:
                        block = source.read(1 << 20)
                        if not block:
                            break
                        target.write(block)
                record = {
                    "profile_index": profile,
                    "profile": data,
                    "status": "VERIFIED_UNSAT",
                    "variables": model.variables,
                    "clauses": len(model.clauses),
                    "cnf_sha256": cnf_sha,
                    "profiles_sha256": profiles_sha,
                    "proof_lines": len(trace),
                    "proof_sha256": proof_sha,
                    "proof_gzip_sha256": sha256(compressed),
                    "proof_gzip_bytes": compressed.stat().st_size,
                    "checker_stdout": checked.stdout.strip(),
                }
                proof.unlink()
        atomic_json(results / f"profile_{profile:02d}.json", record)
        records.append(record)
        cnf.unlink()
        print("RESULT_JSON " + json.dumps(record, sort_keys=True), flush=True)

    manifest = {
        "PASS": True,
        "shard_index": args.shard_index,
        "shard_count": args.shard_count,
        "profile_ids": profile_ids,
        "status_histogram": {
            status: sum(record["status"] == status for record in records)
            for status in sorted({record["status"] for record in records})
        },
    }
    atomic_json(args.out / f"parity_shard_{args.shard_index:02d}.json", manifest)


if __name__ == "__main__":
    main()
