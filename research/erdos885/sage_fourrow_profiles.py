#!/usr/bin/env python3
"""Screen and certify the five elliptic quotient ranks for the three four-row
curves containing the unique rank-2 triple [2578, 5553, 5922].

Each factor is isolated: a difficult descent is reported, not allowed to erase
certificates already completed for the other factors.
"""
from __future__ import annotations

import itertools
import json
import time
import traceback
from pathlib import Path

from sage.all import EllipticCurve, Integer, QQ, proof

BASE = [2578, 5553, 5922]
EXTRA = [2422, 3222, 8678]


def triple_curve(rows):
    a, b, c = map(Integer, rows)
    p = b*b-a*a
    q = c*c-a*a
    return EllipticCurve(QQ, [0, 4*(p+q), 0, 16*p*q, 0]).global_minimal_model()


def quartic_curve(rows):
    a, b, c, d = map(Integer, rows)
    B = 4*(b*b-a*a)
    C = 4*(c*c-a*a)
    D = 4*(d*d-a*a)
    A = B*C*D
    S1 = B+C+D
    S2 = B*C+B*D+C*D
    return EllipticCurve(QQ, [0, S2, 0, A*S1, A*A]).global_minimal_model()


def screen(E):
    started=time.time()
    r={"minimal_ainvs":[str(x) for x in E.a_invariants()]}
    try:
        proof.all(False)
        gs=E.gens(proof=False)
        r["rank_lower_bound_from_gens"]=len(gs)
        r["rank_heuristic"]=int(E.rank(proof=False))
        r["gens_certain_after_heuristic"]=bool(E.gens_certain())
    except Exception as exc:
        r["heuristic_error"]=f"{type(exc).__name__}: {exc}"
    try:
        proof.all(True)
        r["rank_proved"]=int(E.rank(proof=True))
        r["rank_proved_success"]=True
    except Exception as exc:
        r["rank_proved_success"]=False
        r["rank_proved_error"]=f"{type(exc).__name__}: {exc}"
        r["rank_proved_traceback"]=traceback.format_exc(limit=6)
    finally:
        proof.all(True)
    try:
        r["root_number"]=str(E.root_number())
    except Exception as exc:
        r["root_number_error"]=f"{type(exc).__name__}: {exc}"
    r["elapsed_seconds"]=round(time.time()-started,3)
    return r


out=[]
for d in EXTRA:
    rows=BASE+[d]
    entry={"rows":rows,"triple_factors":[]}
    for inds in itertools.combinations(range(4),3):
        rr=[rows[i] for i in inds]
        item={"indices":list(inds),"rows":rr}
        try:
            item.update(screen(triple_curve(rr)))
        except Exception as exc:
            item["curve_error"]=f"{type(exc).__name__}: {exc}"
            item["curve_traceback"]=traceback.format_exc(limit=6)
        entry["triple_factors"].append(item)
    try:
        entry["quartic_factor"]=screen(quartic_curve(rows))
    except Exception as exc:
        entry["quartic_factor"]={
            "curve_error":f"{type(exc).__name__}: {exc}",
            "curve_traceback":traceback.format_exc(limit=6),
        }
    entry["rank_profile_proved"]=[
        x.get("rank_proved") for x in entry["triple_factors"]
    ]+[entry["quartic_factor"].get("rank_proved")]
    out.append(entry)

Path("results").mkdir(exist_ok=True)
Path("results/fourrow_profiles.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
print(json.dumps(out,sort_keys=True))
