#!/usr/bin/env python3
"""Solve and independently check a deterministic shard of weight-48 lift CNFs."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import time
from pathlib import Path

from pysat.solvers import Solver

from model import make_root_model
from s84_weight48_translation_sat import (
    LiftModel,
    load_representatives,
    write_dimacs,
)
from verify import verify_reduced


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
    parser.add_argument("--representatives", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--shard-index", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--solver", default="glucose4")
    args = parser.parse_args()

    data = load_representatives(args.representatives)
    orbit_ids = [
        orbit
        for orbit in range(90)
        if orbit % args.shard_count == args.shard_index
    ]
    args.out.mkdir(parents=True, exist_ok=True)
    results = args.out / "results"
    proofs = args.out / "proofs"
    work = args.out / "work"
    results.mkdir(exist_ok=True)
    proofs.mkdir(exist_ok=True)
    work.mkdir(exist_ok=True)

    representatives_sha = sha256(args.representatives)
    started = time.time()
    records = []
    for position, orbit in enumerate(orbit_ids, 1):
        build_started = time.time()
        model = LiftModel(list(map(int, data["representatives"][orbit])))
        variables, clauses, domain_literals = model.encode_cnf()
        build_seconds = time.time() - build_started
        cnf = work / f"orbit_{orbit:02d}.cnf"
        proof = work / f"orbit_{orbit:02d}.drup"
        write_dimacs(cnf, variables, clauses)
        cnf_sha = sha256(cnf)

        solve_started = time.time()
        with Solver(
            name=args.solver,
            bootstrap_with=clauses,
            with_proof=True,
        ) as solver:
            satisfiable = solver.solve()
            solve_seconds = time.time() - solve_started
            if satisfiable:
                positive = {literal for literal in solver.get_model() if literal > 0}
                translations = []
                for edge_variable in model.edge_variables:
                    values = [
                        value
                        for value, literal in enumerate(domain_literals[edge_variable])
                        if literal in positive
                    ]
                    assert len(values) == 1
                    translations.append(values[0])
                edges = model.reconstruct_edges(translations)
                verify_reduced(make_root_model(14), edges)
                witness = args.out / f"orbit_{orbit:02d}_witness.json"
                witness.write_text(
                    json.dumps(
                        {
                            "k": 14,
                            "orbit": orbit,
                            "translations": translations,
                            "edges": [list(edge) for edge in edges],
                        },
                        indent=2,
                        sort_keys=True,
                    )
                    + "\n"
                )
                record = {
                    "orbit": orbit,
                    "status": "SAT_VERIFIED_WITNESS",
                    "witness": str(witness),
                    "witness_sha256": sha256(witness),
                    "variables": variables,
                    "clauses": len(clauses),
                    "cnf_sha256": cnf_sha,
                    "representatives_sha256": representatives_sha,
                    "build_seconds": build_seconds,
                    "solve_seconds": solve_seconds,
                }
                atomic_json(results / f"orbit_{orbit:02d}.json", record)
                raise RuntimeError(f"verified Conway witness in weight-48 orbit {orbit}")
            trace = solver.get_proof()

        if not trace:
            raise RuntimeError(f"UNSAT orbit {orbit} returned no proof")
        proof.write_text("\n".join(trace) + "\n")
        proof_sha = sha256(proof)
        check_started = time.time()
        checked = subprocess.run(
            [str(args.checker), str(cnf), str(proof)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=1200,
        )
        check_seconds = time.time() - check_started
        if checked.returncode or "s VERIFIED" not in checked.stdout:
            record = {
                "orbit": orbit,
                "status": "CHECK_FAILED",
                "proof_sha256": proof_sha,
                "checker_stdout": checked.stdout,
                "checker_stderr": checked.stderr,
            }
            atomic_json(results / f"orbit_{orbit:02d}.json", record)
            raise RuntimeError(f"proof replay failed for weight-48 orbit {orbit}")

        compressed = proofs / f"orbit_{orbit:02d}.drup.gz"
        with proof.open("rb") as source, gzip.open(compressed, "wb", compresslevel=6) as target:
            while True:
                block = source.read(1 << 20)
                if not block:
                    break
                target.write(block)

        record = {
            "orbit": orbit,
            "status": "VERIFIED_UNSAT",
            "solver": args.solver,
            "variables": variables,
            "clauses": len(clauses),
            "table_size_histogram": {
                str(size): sum(len(table) == size for table in model.tables)
                for size in sorted(set(map(len, model.tables)))
            },
            "cnf_sha256": cnf_sha,
            "proof_sha256": proof_sha,
            "proof_lines": len(trace),
            "proof_gzip_sha256": sha256(compressed),
            "proof_gzip_bytes": compressed.stat().st_size,
            "representatives_sha256": representatives_sha,
            "build_seconds": build_seconds,
            "solve_seconds": solve_seconds,
            "check_seconds": check_seconds,
            "checker_stdout": checked.stdout.strip(),
        }
        atomic_json(results / f"orbit_{orbit:02d}.json", record)
        records.append(record)
        cnf.unlink()
        proof.unlink()
        print(
            json.dumps(
                {
                    "event": "verified",
                    "shard": args.shard_index,
                    "position": position,
                    "count": len(orbit_ids),
                    "orbit": orbit,
                    "variables": variables,
                    "clauses": len(clauses),
                    "proof_lines": len(trace),
                    "build_seconds": build_seconds,
                    "solve_seconds": solve_seconds,
                    "check_seconds": check_seconds,
                },
                sort_keys=True,
            ),
            flush=True,
        )

    manifest = {
        "PASS": True,
        "shard_index": args.shard_index,
        "shard_count": args.shard_count,
        "orbit_ids": orbit_ids,
        "verified": len(records),
        "representatives_sha256": representatives_sha,
        "elapsed_seconds": time.time() - started,
    }
    atomic_json(args.out / f"shard_{args.shard_index:02d}.json", manifest)


if __name__ == "__main__":
    main()
