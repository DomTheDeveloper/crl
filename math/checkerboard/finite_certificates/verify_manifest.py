#!/usr/bin/env python3
"""Verify committed construction hashes and generated instance metadata."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("manifest.json"))
    parser.add_argument("--metadata", type=Path, nargs="*", default=[])
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    assert manifest["format"] == "checkerboard-finite-certificate-manifest-v1"
    root = args.manifest.parent

    for entry in manifest["construction_certificates"]:
        path = root / entry["path"]
        payload = json.loads(path.read_text(encoding="utf-8"))
        assert sha256(path) == entry["sha256"], path
        assert payload["format"] == "checkerboard-ntil-construction-v1"
        assert int(payload["n"]) == int(entry["n"])
        assert int(payload["parity"]) == int(entry["parity"])
        assert int(payload["size"]) == int(entry["size"])
        assert len(payload["points"]) == int(entry["size"])
        exact = manifest["exact_values"][str(entry["n"])][str(entry["parity"])]
        assert int(exact) == int(entry["size"])
        print(f"PASS construction={path.name} sha256={entry['sha256']}")

    index = {(int(entry["n"]), int(entry["parity"]), int(entry["excluded_size"])): entry
             for entry in manifest["upper_instances"]}
    for path in args.metadata:
        metadata = json.loads(path.read_text(encoding="utf-8"))
        target = int(metadata.get("minimum_selected", metadata.get("target")))
        key = (int(metadata["n"]), int(metadata["parity"]), target)
        entry = index[key]
        assert metadata["cnf_sha256"] == entry["cnf_sha256"]
        assert int(metadata["variable_count"]) == int(entry["variables"])
        assert int(metadata["clause_count"]) == int(entry["clauses"])
        if "candidate_points" in entry:
            assert int(metadata["candidate_count"]) == int(entry["candidate_points"])
        print(f"PASS instance=n{key[0]}-p{key[1]}-k{key[2]} sha256={entry['cnf_sha256']}")

    print("ALL CHECKERBOARD CERTIFICATE MANIFEST ENTRIES VERIFIED")


if __name__ == "__main__":
    main()
