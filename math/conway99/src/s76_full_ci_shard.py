#!/usr/bin/env python3
"""Solve and independently check one deterministic shard of all 701 ``s=76`` branches.

UNSAT is accepted only after a deletion-aware RUP checker validates the emitted
proof against the exact branch CNF.  SAT is accepted only after reconstructing
the selected reduced edges and running both independent exact graph verifiers.
Timeouts and process failures are recorded as incomplete, never as mathematics.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import time
from collections import Counter
from itertools import combinations
from pathlib import Path

from deficit_branch_sat import (
    CELLS,
    MEMBERS,
    N,
    cell,
    intersection,
    key,
    normalize_state,
    transition_edges,
)
from model import make_root_model
from verify import verify_reduced
from verify_matrix import verify_matrix


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


def d_variable_pairs(state) -> list[tuple[int, int]]:
    """Reproduce the initial IDPool allocation in ``deficit_branch_sat.build``."""
    selected = transition_edges(state)
    intact = []
    affected = []
    for fiber in CELLS:
        vertices = MEMBERS[fiber]
        internal = [
            key(left, right)
            for left, right in combinations(vertices, 2)
            if key(left, right) in selected
        ]
        degrees = Counter()
        for left, right in internal:
            degrees[left] += 1
            degrees[right] += 1
        target = intact if len(internal) == 4 and all(degrees[v] == 2 for v in vertices) else affected
        target.append(fiber)
    affected = set(affected)

    pairs = []
    for left, right in combinations(range(N), 2):
        if intersection(left, right):
            continue
        left_fiber, right_fiber = cell(left), cell(right)
        if set(left_fiber).isdisjoint(right_fiber) or (
            left_fiber in affected and right_fiber in affected
        ):
            pairs.append((left, right))
    return pairs


def verify_sat_model(state, raw_model: Path, witness: Path) -> dict[str, object]:
    payload = json.loads(raw_model.read_text())
    positive = {int(value) for value in payload["model"] if int(value) > 0}
    pairs = d_variable_pairs(state)
    selected = set(transition_edges(state))
    selected.update(pair for variable, pair in enumerate(pairs, 1) if variable in positive)
    edges = sorted(selected)

    root_model = make_root_model(14)
    verify_reduced(root_model, edges)
    verify_matrix(14, edges)
    witness.write_text(
        json.dumps(
            {"k": 14, "edges": [list(edge) for edge in edges]},
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    return {
        "reduced_edges": len(edges),
        "witness_sha256": sha256(witness),
        "verified_by": ["combinatorial", "integer-matrix"],
    }


def parse_result(stdout: str) -> dict[str, object]:
    rows = [line for line in stdout.splitlines() if line.startswith("RESULT_JSON ")]
    if not rows:
        raise RuntimeError("branch solver emitted no RESULT_JSON line")
    return json.loads(rows[-1].split(" ", 1)[1])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--representatives", type=Path, required=True)
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--shard-index", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--solver", default="glucose4")
    parser.add_argument("--solve-timeout", type=float, default=1200)
    parser.add_argument("--check-timeout", type=float, default=900)
    args = parser.parse_args()

    representatives = json.loads(args.representatives.read_text())
    profiles = json.loads(args.profiles.read_text())
    mapping = [int(value) for value in profiles["branch_profile_indices"]]
    assert len(representatives) == len(mapping) == 701
    assert profiles["S7_intact_core_orbits"] == 41

    results = args.out / "results"
    proofs = args.out / "proofs"
    witnesses = args.out / "witnesses"
    work = args.out / "work"
    for directory in (results, proofs, witnesses, work):
        directory.mkdir(parents=True, exist_ok=True)

    orbit_ids = [
        orbit for orbit in range(701) if orbit % args.shard_count == args.shard_index
    ]
    records = []
    solver_script = Path(__file__).with_name("deficit_branch_sat.py")

    for position, orbit in enumerate(orbit_ids, 1):
        started = time.time()
        state = normalize_state(representatives[orbit])
        cnf = work / f"orbit_{orbit:03d}.cnf"
        proof = work / f"orbit_{orbit:03d}.drup"
        raw_model = work / f"orbit_{orbit:03d}.model.json"
        command = [
            sys.executable,
            str(solver_script),
            "--representatives",
            str(args.representatives),
            "--orbit",
            str(orbit),
            "--cnf",
            str(cnf),
            "--solver",
            args.solver,
            "--proof",
            str(proof),
            "--witness",
            str(raw_model),
        ]
        record: dict[str, object] = {
            "orbit": orbit,
            "profile_index": mapping[orbit],
            "shard_index": args.shard_index,
            "shard_count": args.shard_count,
            "shard_position": position,
            "shard_orbits": len(orbit_ids),
        }
        try:
            completed = subprocess.run(
                command,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=args.solve_timeout,
            )
            record["solver_stdout"] = completed.stdout[-20_000:]
            record["solver_stderr"] = completed.stderr[-20_000:]
            if completed.returncode != 0:
                raise RuntimeError(f"solver process returned {completed.returncode}")
            solver_result = parse_result(completed.stdout)
            record["solver_result"] = solver_result
            status = solver_result["status"]

            if status in ("UNSAT", "UNSAT_ROOT"):
                assert cnf.is_file() and proof.is_file()
                checked = subprocess.run(
                    [str(args.checker), str(cnf), str(proof)],
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=args.check_timeout,
                )
                if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
                    raise RuntimeError(
                        "proof checker rejected trace: " + checked.stdout + checked.stderr
                    )
                cnf_gz = proofs / f"orbit_{orbit:03d}.cnf.gz"
                proof_gz = proofs / f"orbit_{orbit:03d}.drup.gz"
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
            elif status == "SAT":
                assert raw_model.is_file()
                witness = witnesses / f"orbit_{orbit:03d}.json"
                verified = verify_sat_model(state, raw_model, witness)
                record.update(status="VERIFIED_SAT", **verified)
            else:
                record["status"] = f"UNEXPECTED_{status}"
        except subprocess.TimeoutExpired as error:
            record.update(
                status="TIMEOUT_NO_RESULT",
                timeout_seconds=args.solve_timeout,
                timeout_stdout=(error.stdout or "")[-20_000:] if isinstance(error.stdout, str) else "",
                timeout_stderr=(error.stderr or "")[-20_000:] if isinstance(error.stderr, str) else "",
            )
        except Exception as error:  # retained as an explicit non-result
            record.update(status="ERROR_NO_RESULT", error=repr(error))
        finally:
            record["elapsed_seconds"] = time.time() - started
            atomic_json(results / f"orbit_{orbit:03d}.json", record)
            records.append(record)
            for path in (cnf, proof, raw_model):
                if path.exists():
                    path.unlink()
            print("RESULT_JSON " + json.dumps(record, sort_keys=True), flush=True)

    manifest = {
        "PASS": True,
        "purpose": "proof-producing full fixed-transition s=76 search",
        "shard_index": args.shard_index,
        "shard_count": args.shard_count,
        "orbit_ids": orbit_ids,
        "orbits_completed": len(records),
        "status_histogram": {
            status: sum(record["status"] == status for record in records)
            for status in sorted({str(record["status"]) for record in records})
        },
    }
    atomic_json(args.out / f"shard_{args.shard_index:02d}.json", manifest)


if __name__ == "__main__":
    main()
