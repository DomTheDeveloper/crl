#!/usr/bin/env python3
"""Audit adaptive_top.py JSONL manifests for complete canonical coverage.

This checks the integrity of the search ledger, not the SAT solver's UNSAT
claims.  Final mathematical verification still requires DRAT/LRAT/VeriPB
certificates for every UNSAT instance or one proof for the unsplit top CNF.
"""

from __future__ import annotations

import argparse
import glob
import json
from collections import Counter
from pathlib import Path

import n22_data as data


def load_summary(path: Path) -> tuple[list[dict], dict]:
    rows: list[dict] = []
    with path.open() as handle:
        for line_number, line in enumerate(handle, 1):
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise SystemExit(f"{path}:{line_number}: invalid JSON: {exc}") from exc
    summaries = [row for row in rows if row.get("event") == "shard_summary"]
    if len(summaries) != 1:
        raise SystemExit(f"{path}: expected one shard_summary, found {len(summaries)}")
    return rows, summaries[0]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("top", type=int)
    parser.add_argument("pattern", help="glob matching the shard JSONL files")
    parser.add_argument("--shards", type=int, default=8)
    args = parser.parse_args()

    paths = [Path(name) for name in sorted(glob.glob(args.pattern))]
    if len(paths) != args.shards:
        raise SystemExit(f"expected {args.shards} files, found {len(paths)}")

    allowed = [mask for mask in data.DOUBLES if mask >= args.top]
    expected_lefts = [mask for mask in allowed if (mask & 1) == (args.top & 1)]
    seen_lefts: list[int] = []
    aggregate: Counter[str] = Counter()
    elapsed = 0.0

    for path in paths:
        rows, summary = load_summary(path)
        if summary.get("top") != args.top:
            raise SystemExit(f"{path}: wrong top mask {summary.get('top')}")
        shard = summary.get("shard")
        if not isinstance(shard, int) or not 0 <= shard < args.shards:
            raise SystemExit(f"{path}: invalid shard {shard}")
        expected_assigned = [m for i, m in enumerate(expected_lefts) if i % args.shards == shard]
        if summary.get("assigned_lefts") != expected_assigned:
            raise SystemExit(
                f"{path}: assigned_lefts mismatch\n"
                f"expected {expected_assigned}\nactual   {summary.get('assigned_lefts')}"
            )
        if summary.get("unknown"):
            raise SystemExit(f"{path}: contains UNKNOWN branches")
        if summary.get("closed") is not True:
            raise SystemExit(f"{path}: shard is not marked closed")
        if any(row.get("event") == "WITNESS" for row in rows):
            raise SystemExit(f"{path}: contains a witness event")
        if any(row.get("status") == "UNKNOWN" for row in rows):
            raise SystemExit(f"{path}: contains an UNKNOWN event")

        event_counts = Counter()
        for row in rows:
            event = row.get("event")
            if event == "left" and row.get("status") == "UNSAT":
                event_counts["left_unsat"] += 1
            elif event == "rb" and row.get("status") == "UNSAT":
                event_counts["rb_unsat"] += 1
            elif event == "leaf" and row.get("status") == "UNSAT":
                event_counts["leaf_unsat"] += 1
        recorded = summary.get("counts", {})
        for key in ("left_unsat", "rb_unsat", "leaf_unsat"):
            if event_counts[key] != recorded.get(key):
                raise SystemExit(
                    f"{path}: {key} mismatch: events={event_counts[key]} summary={recorded.get(key)}"
                )

        seen_lefts.extend(expected_assigned)
        aggregate.update(recorded)
        elapsed += float(summary.get("elapsed", 0.0))

    if sorted(seen_lefts) != sorted(expected_lefts):
        raise SystemExit("the shard union does not cover every expected left mask exactly once")

    result = {
        "top": args.top,
        "shards": args.shards,
        "closed": True,
        "expected_lefts": len(expected_lefts),
        "counts": dict(aggregate),
        "elapsed_seconds": elapsed,
        "files": [str(path) for path in paths],
        "trust_boundary": "manifest integrity only; UNSAT claims still require proof certificates",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
