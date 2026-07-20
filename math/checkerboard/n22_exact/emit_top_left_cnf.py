#!/usr/bin/env python3
"""Emit one exact all-double top/left boundary subfamily for DRAT certification.

The union over every two-bit left mask numerically at least the fixed canonical
`top` mask is exactly the complete `build_double(top)` family: `build_double`
already enforces two selected points on every boundary and excludes all other
boundary masks smaller than `top`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import n22_data as data
import n22_exact_core as core


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("top", type=int)
    parser.add_argument("left", type=int)
    parser.add_argument("output", type=Path)
    parser.add_argument("--manifest", type=Path, default=None)
    args = parser.parse_args()

    if args.top not in data.DOUBLES:
        raise SystemExit(f"top mask {args.top} is not a two-point boundary mask")
    if args.left not in data.DOUBLES:
        raise SystemExit(f"left mask {args.left} is not a two-point boundary mask")
    if args.left < args.top:
        raise SystemExit(
            f"left mask {args.left} is excluded by canonical top mask {args.top}"
        )

    cnf, info = core.build_double(args.top)
    selected = []
    for i, var in enumerate(data.BIDS["left"]):
        bit = (args.left >> i) & 1
        cnf.append([var if bit else -var])
        if bit:
            selected.append(i)

    if len(selected) != 2:
        raise AssertionError(selected)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    cnf.to_file(str(args.output))
    manifest = {
        "top": args.top,
        "left": args.left,
        "left_selected_indices": selected,
        "canonical_left_condition": f"left >= {args.top}",
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
