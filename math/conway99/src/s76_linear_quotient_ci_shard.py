#!/usr/bin/env python3
"""Solve and independently check one shard of 41 proof-producing S3 quotients."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path


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


def gzip_file(source: Path, target: Path) -> None:
    with source.open("rb") as incoming, gzip.open(target, "wb", compresslevel=6) as outgoing:
        for block in iter(lambda: incoming.read(1 << 20), b""):
            outgoing.write(block)


def parse_result(stdout: str) -> dict[str, object]:
    rows = [line for line in stdout.splitlines() if line.startswith("RESULT_JSON ")]
    if not rows:
        raise RuntimeError("quotient solver emitted no RESULT_JSON line")
    return json.loads(rows[-1].split(" ", 1)[1])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--shard-index", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--solver", default="glucose4")
    parser.add_argument("--timeout", type=float, default=1800)
    args = parser.parse_args()

    report = json.loads(args.profiles.read_text())
    assert report["PASS"] and len(report["profiles"]) == 41
    results = args.out / "linear_results"
    proofs = args.out / "linear_proofs"
    assignments = args.out / "linear_assignments"
    work = args.out / "work"
    for directory in (results, proofs, assignments, work):
        directory.mkdir(parents=True, exist_ok=True)

    profile_ids = [
        profile for profile in range(41) if profile % args.shard_count == args.shard_index
    ]
    records = []
    solver_script = Path(__file__).with_name("s76_linear_quotient_sat.py")
    for position, profile in enumerate(profile_ids, 1):
        cnf = work / f"profile_{profile:02d}.cnf"
        proof = work / f"profile_{profile:02d}.drup"
        assignment = assignments / f"profile_{profile:02d}.json"
        command = [
            sys.executable,
            str(solver_script),
            "--profiles",
            str(args.profiles),
            "--profile",
            str(profile),
            "--cnf",
            str(cnf),
            "--solver",
            args.solver,
            "--proof",
            str(proof),
            "--assignment",
            str(assignment),
        ]
        record: dict[str, object] = {
            "profile_index": profile,
            "profile": report["profiles"][profile],
            "shard_index": args.shard_index,
            "shard_count": args.shard_count,
            "shard_position": position,
            "shard_profiles": len(profile_ids),
        }
        try:
            completed = subprocess.run(
                command,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=args.timeout,
            )
            record["solver_stdout"] = completed.stdout[-20_000:]
            record["solver_stderr"] = completed.stderr[-20_000:]
            if completed.returncode != 0:
                raise RuntimeError(f"solver process returned {completed.returncode}")
            result = parse_result(completed.stdout)
            assert result["profile_index"] == profile
            status = result["status"]
            record["solver_result"] = result
            if status == "UNSAT":
                assert cnf.is_file() and proof.is_file()
                checked = subprocess.run(
                    [str(args.checker), str(cnf), str(proof)],
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=args.timeout,
                )
                if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
                    raise RuntimeError("proof checker rejected trace: " + checked.stdout + checked.stderr)
                cnf_gz = proofs / f"profile_{profile:02d}.cnf.gz"
                proof_gz = proofs / f"profile_{profile:02d}.drup.gz"
                gzip_file(cnf, cnf_gz)
                gzip_file(proof, proof_gz)
                record.update(
                    status="VERIFIED_UNSAT",
                    cnf_sha256=sha256(cnf),
                    proof_sha256=sha256(proof),
                    cnf_gzip_sha256=sha256(cnf_gz),
                    proof_gzip_sha256=sha256(proof_gz),
                    proof_checker_stdout=checked.stdout.strip(),
                )
                if assignment.exists():
                    assignment.unlink()
            elif status == "SAT":
                assert assignment.is_file()
                assert result.get("verified_assignment")
                record.update(
                    status="VERIFIED_SAT",
                    assignment_sha256=sha256(assignment),
                )
            else:
                record["status"] = f"UNEXPECTED_{status}"
        except subprocess.TimeoutExpired:
            record.update(status="TIMEOUT_NO_RESULT", timeout_seconds=args.timeout)
        except Exception as error:
            record.update(status="ERROR_NO_RESULT", error=repr(error))
        finally:
            atomic_json(results / f"profile_{profile:02d}.json", record)
            records.append(record)
            for path in (cnf, proof):
                if path.exists():
                    path.unlink()
            print("RESULT_JSON " + json.dumps(record, sort_keys=True), flush=True)

    manifest = {
        "PASS": True,
        "purpose": "proof-producing position-sensitive S3 quotient",
        "shard_index": args.shard_index,
        "shard_count": args.shard_count,
        "profile_ids": profile_ids,
        "profiles_completed": len(records),
        "status_histogram": {
            status: sum(record["status"] == status for record in records)
            for status in sorted({str(record["status"]) for record in records})
        },
    }
    atomic_json(args.out / f"linear_shard_{args.shard_index:02d}.json", manifest)


if __name__ == "__main__":
    main()
