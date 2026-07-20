#!/usr/bin/env python3
"""Emit the unrestricted exact 34-point CNF for the even checkerboard class of 22x22."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from pysat.formula import IDPool

import n22_exact_core as core


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path, help="DIMACS output path")
    parser.add_argument("--manifest", type=Path, default=None)
    args = parser.parse_args()

    pool = IDPool(start_from=243)
    cnf, info = core.base_cnf(pool)
    cnf.nv = max(cnf.nv, pool.top)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cnf.to_file(str(args.output))

    manifest = {
        "board_side": 22,
        "parity": 0,
        "target_points": 34,
        "boundary_restrictions": None,
        "variables": cnf.nv,
        "clauses": len(cnf.clauses),
        "weighted_slack_encoding": info,
        "cnf": str(args.output),
        "equivalence_note": (
            "This is the unrestricted target-34 encoding: exact cardinality 34, "
            "all Euclidean line capacity-two clauses, and the weighted slack identity "
            "algebraically implied by those constraints and the exact dual cover."
        ),
    }
    text = json.dumps(manifest, sort_keys=True, indent=2) + "\n"
    if args.manifest is not None:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(text)
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
