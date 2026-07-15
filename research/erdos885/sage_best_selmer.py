#!/usr/bin/env python3
"""Compute exact 2-Selmer diagnostics for the best genus-5 row curve.

The curve uses rows [2578, 5553, 5922, 3222] and has certified elliptic-factor
rank profile [2,4,4,3,4].  For each factor we record the proved rank, rational
2-torsion dimension, and Sage/PARI 2-Selmer rank.  The difference

  selmer_dim - rank - dim(E(Q)[2])

is the dimension of the 2-primary Tate-Shafarevich contribution when the
reported quantities are exact.
"""
from __future__ import annotations

import itertools
import json
import math
import traceback
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof

ROWS = [2578, 5553, 5922, 3222]


def triple_curve(rows):
    a,b,c=map(Integer,rows)
    p=b*b-a*a; q=c*c-a*a
    return EllipticCurve(QQ,[0,4*(p+q),0,16*p*q,0]).global_minimal_model()


def quartic_curve(rows):
    a,b,c,d=map(Integer,rows)
    B=4*(b*b-a*a); C=4*(c*c-a*a); D=4*(d*d-a*a)
    A=B*C*D; S1=B+C+D; S2=B*C+B*D+C*D
    return EllipticCurve(QQ,[0,S2,0,A*S1,A*A]).global_minimal_model()


def v2(n):
    n=Integer(n); e=0
    while n and n%2==0: n//=2; e+=1
    return e


def diagnose(label,rows,E):
    out={"label":label,"rows":rows,"minimal_ainvs":[str(x) for x in E.a_invariants()]}
    try:
        proof.all(True)
        out["rank_proved"]=int(E.rank(proof=True))
    except Exception as exc:
        out["rank_error"]=f"{type(exc).__name__}: {exc}"
    try:
        tors=int(E.torsion_order())
        out["torsion_order"]=tors
        out["two_torsion_dimension"]=v2(tors)
    except Exception as exc:
        out["torsion_error"]=f"{type(exc).__name__}: {exc}"
    for alg in ["pari","mwrank"]:
        try:
            out[f"selmer_rank_{alg}"]=int(E.selmer_rank(algorithm=alg))
        except Exception as exc:
            out[f"selmer_rank_{alg}_error"]=f"{type(exc).__name__}: {exc}"
            out[f"selmer_rank_{alg}_traceback"]=traceback.format_exc(limit=5)
    if all(k in out for k in ["rank_proved","two_torsion_dimension","selmer_rank_pari"]):
        out["sha_two_dimension_from_pari"]=(
            out["selmer_rank_pari"]-out["rank_proved"]-out["two_torsion_dimension"]
        )
    return out


result={"rows":ROWS,"factors":[]}
for inds in itertools.combinations(range(4),3):
    rr=[ROWS[i] for i in inds]
    result["factors"].append(diagnose(f"triple_{inds}",rr,triple_curve(rr)))
result["factors"].append(diagnose("quartic_all",ROWS,quartic_curve(ROWS)))
Path("results").mkdir(exist_ok=True)
Path("results/best_selmer.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
print(json.dumps(result,sort_keys=True))
