#!/usr/bin/env python3
"""Expand the exact generated Handelman proof source.

The payload is gzip-compressed only to keep the repository connector and diffs
manageable.  It expands to a human-readable Lean module.  The expanded source
is not trusted: Lean checks every coefficient sign, polynomial identity,
Farkas implication, cell case, and the final global obstacle theorem.
"""

from __future__ import annotations

import base64
import gzip
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PARTS = [
    ROOT / "math/checkerboard/lp/certificates/dual_handelman_payload_0.txt",
    ROOT / "math/checkerboard/lp/certificates/dual_handelman_payload_1.txt",
    ROOT / "math/checkerboard/lp/certificates/dual_handelman_payload_2.txt",
]
OUTPUT = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/DualHandelmanData.lean"
EXPECTED_SHA256 = "258056bf2cded9ea19b5419f4f3a837e6476373d7594b4158b7d54accba0febf"
EXPECTED_LINES = 10589


def main() -> None:
    encoded = "".join(path.read_text(encoding="ascii").strip() for path in PARTS)
    source = gzip.decompress(base64.b64decode(encoded))
    digest = hashlib.sha256(source).hexdigest()
    if digest != EXPECTED_SHA256:
        raise SystemExit(
            f"dual Handelman payload checksum mismatch: {digest} != {EXPECTED_SHA256}"
        )
    text = source.decode("utf-8")
    line_count = len(text.splitlines())
    if line_count != EXPECTED_LINES:
        raise SystemExit(
            f"dual Handelman source line count mismatch: {line_count} != {EXPECTED_LINES}"
        )
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUTPUT} ({line_count} lines, sha256={digest})")


if __name__ == "__main__":
    main()
