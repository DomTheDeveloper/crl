#!/usr/bin/env python3
"""Emit one complete canonical top-boundary CNF for proof-producing SAT runs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import n22_exact_core as core


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("top", type=int, help="canonical 11-bit top boundary mask")
    parser.add_argument("output", type=Path, help="DIMACS output path")
    parser.add_argument("--manifest", type=Path, default=None)
    args = parser.parse_args()

    cnf, info = core.build_double(args.top)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cnf.to_file(str(args.output))

    manifest = {
        "top": args.top,
        "variables": cnf.nv,
        "clauses": len(cnf.clauses),
        "pb": info,
        "cnf": str(args.output),
    }
    text = json.dumps(manifest, sort_keys=True, indent=2) + "\n"
    if args.manifest is not None:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(text)
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
