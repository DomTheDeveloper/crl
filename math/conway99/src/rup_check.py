#!/usr/bin/env python3
"""Small, independent DRUP/RUP checker.

Every added clause must be reverse-unit-propagation valid; deletion lines are
honored. The final active formula must unit-propagate to contradiction. This
checker deliberately rejects proofs requiring the more general RAT rule.
For very large certificates, also use a mature independently built checker
such as drat-trim or an LRAT checker.
"""
from __future__ import annotations
import argparse, json

def parse_cnf(path):
    clauses = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "cp":
                continue
            clauses.append(tuple(int(x) for x in line.split() if int(x) != 0))
    return clauses

def unit_conflict(clauses, assumptions=()):
    value = {}
    for lit in assumptions:
        var, val = abs(lit), lit > 0
        if var in value and value[var] != val:
            return True
        value[var] = val
    changed = True
    while changed:
        changed = False
        for clause in clauses:
            satisfied = False
            unresolved = []
            for lit in clause:
                var = abs(lit)
                if var not in value:
                    unresolved.append(lit)
                elif value[var] == (lit > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not unresolved:
                return True
            if len(unresolved) == 1:
                lit = unresolved[0]
                var, val = abs(lit), lit > 0
                if var in value:
                    if value[var] != val:
                        return True
                else:
                    value[var] = val
                    changed = True
    return False

def check(cnf_path, proof_path):
    active = parse_cnf(cnf_path)
    additions = deletions = 0
    with open(proof_path) as f:
        for line_number, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            deletion = line.startswith("d ")
            tokens = line.split()[1:] if deletion else line.split()
            clause = tuple(int(x) for x in tokens if int(x) != 0)
            if deletion:
                try:
                    active.remove(clause)
                except ValueError:
                    pass
                deletions += 1
            else:
                if not unit_conflict(active, (-lit for lit in clause)):
                    raise AssertionError(f"line {line_number} is not RUP: {clause}")
                active.append(clause)
                additions += 1
    assert unit_conflict(active), "final active formula does not unit-propagate to contradiction"
    return {"PASS": True, "additions": additions, "deletions": deletions,
            "active_clauses": len(active)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf")
    ap.add_argument("proof")
    a = ap.parse_args()
    print(json.dumps(check(a.cnf, a.proof), sort_keys=True))

if __name__ == "__main__":
    main()
