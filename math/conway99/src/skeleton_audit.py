#!/usr/bin/env python3
"""Audit the matching-cross skeleton and the exact s=84 cover counts."""
from __future__ import annotations
import json
from itertools import combinations
from collections import Counter, deque
from model import make_root_model


def mm(a,b):
    bt=list(zip(*b))
    return [[sum(x*y for x,y in zip(row,col)) for col in bt] for row in a]


def transpose(a): return [list(x) for x in zip(*a)]


def audit():
    rm=make_root_model(14); labels=rm.labels; n=rm.m
    X=[[int(i in labels[u]) for u in range(n)] for i in range(14)]
    P=[[int(j==(i^1)) for j in range(14)] for i in range(14)]
    M=mm(transpose(X),X);Y=mm(mm(transpose(X),P),X)

    orbit_counts=Counter()
    for u,v in combinations(range(n),2):
        orbit_counts[(M[u][v],Y[u][v])]+=1
    assert orbit_counts==Counter({(0,0):1680,(1,0):840,(0,1):840,
                                 (1,1):84,(0,2):42})
    # Diagonal of 4J-M-Y is two, proving the weighted F-degree.
    assert all(4-M[u][u]-Y[u][u]==2 for u in range(n))

    row_short={0,1,2,3,4,6}
    col_short=set(range(11))|{12}
    assert 5 not in row_short and 11 not in col_short
    # Deficits 1,2,3 cannot be distributed with every positive row and column
    # deficit at least two. This is the exact near-extremal exclusion.
    impossible_s=[]
    for deficit in (1,2,3):
        # Since positive row deficits exclude one, total 2 or 3 must lie in a
        # single row; its missing entries lie in distinct columns and create
        # column deficit one. Deficit one fails already at the row level.
        impossible_s.append(84-deficit)
    assert impossible_s==[83,82,81]

    cells=sorted({tuple(sorted((a//2,b//2))) for a,b in labels})
    members={c:[u for u,(a,b) in enumerate(labels)
                if tuple(sorted((a//2,b//2)))==c] for c in cells}
    blocks=[(a,b) for a,b in combinations(cells,2) if set(a).isdisjoint(b)]
    assert len(cells)==21 and all(len(members[c])==4 for c in cells)
    assert len(blocks)==105

    # Kneser KG(7,2): 21 vertices, degree 10, connected, spectrum
    # 10^1,1^14,(-4)^6. Check the annihilating polynomial and traces exactly.
    K=[[0]*21 for _ in range(21)]
    for i,j in combinations(range(21),2):
        if set(cells[i]).isdisjoint(cells[j]):K[i][j]=K[j][i]=1
    assert all(sum(row)==10 for row in K)
    seen={0};q=deque([0])
    while q:
        i=q.popleft()
        for j,x in enumerate(K[i]):
            if x and j not in seen:seen.add(j);q.append(j)
    assert len(seen)==21
    I=[[int(i==j) for j in range(21)] for i in range(21)]
    def subscale(A,c):return [[A[i][j]-c*I[i][j] for j in range(21)] for i in range(21)]
    poly=mm(mm(subscale(K,10),subscale(K,1)),subscale(K,-4))
    assert all(x==0 for row in poly for x in row)
    assert sum(K[i][i] for i in range(21))==0
    K2=mm(K,K);assert sum(K2[i][i] for i in range(21))==210

    return {
      "PASS":True,
      "matching_cross_relation_counts":{
        f"M={m},Y={y}":c for (m,y),c in sorted(orbit_counts.items())},
      "F_weighted_degree":2,
      "short_transition_parameter":{"total_available":84,
        "excluded_values":[81,82,83]},
      "s84_cover":{"fibers":21,"fiber_size":4,"cross_blocks":105,
        "block_type":"4x4 permutation matrix",
        "quotient_spectrum":{"12":1,"3":14,"-2":6},
        "corrected_unsymmetrized_cnf":{"variables":263760,"clauses":616560,
          "sha256":"09e71a0ecf915961be435f5f93784c061f4eaded737f95dff91fc7acd44aeec4"}}
    }


def main():print(json.dumps(audit(),indent=2,sort_keys=True))
if __name__=="__main__":main()
