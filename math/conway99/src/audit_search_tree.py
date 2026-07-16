#!/usr/bin/env python3
"""Audit logical coverage of a binary cube-and-conquer search manifest.

This verifies partition coverage only. A complete nonexistence proof also
requires every UNSAT leaf proof to validate against the exact leaf CNF and
all file hashes to match.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
from model import SEED_BRANCHES

def normalized(cube):
    c = tuple(int(x) for x in cube)
    assert all(x != 0 for x in c)
    assert len({abs(x) for x in c}) == len(c)
    return c

def audit_node(node, prefix=()):
    cube = normalized(node.get("cube", []))
    assert cube == prefix, (cube, prefix)
    if "split_literal" in node:
        lit = int(node["split_literal"])
        assert lit != 0 and abs(lit) not in {abs(x) for x in prefix}
        children = node.get("children", [])
        assert len(children) == 2
        child_cubes = {normalized(ch["cube"]): ch for ch in children}
        expected = {prefix + (lit,), prefix + (-lit,)}
        assert set(child_cubes) == expected
        leaves = 0
        for child_prefix in expected:
            leaves += audit_node(child_cubes[child_prefix], child_prefix)
        return leaves
    status = node.get("status")
    assert status in {"SAT", "UNSAT"}
    if status == "SAT":
        assert node.get("witness_sha256")
    else:
        assert node.get("cnf_sha256") and node.get("proof_sha256")
        assert node.get("proof_checked") is True
    return 1

def audit_manifest(data):
    assert data.get("problem") == "Conway99"
    branches = data.get("branches", {})
    assert set(branches) == set(SEED_BRANCHES)
    total = sum(audit_node(branches[name], ()) for name in sorted(branches))
    return {"PASS": True, "branches": len(branches), "terminal_leaves": total}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest")
    a = ap.parse_args()
    data = json.loads(Path(a.manifest).read_text())
    print(json.dumps(audit_manifest(data), sort_keys=True))

if __name__ == "__main__":
    main()
