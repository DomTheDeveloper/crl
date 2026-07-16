#!/usr/bin/env python3
"""Independent structural verifier for a reduced Conway-99 witness.

The input is JSON `{\"k\": 14, \"edges\": [[u,v], ...]}` using the canonical
84 labels. This checker is intentionally independent of model.py and of the
existing common-neighbor verifiers.
"""
from __future__ import annotations
import argparse, json
from itertools import combinations
from pathlib import Path


def mm(a,b):
    bt=list(zip(*b))
    return [[sum(x*y for x,y in zip(row,col)) for col in bt] for row in a]

def add_scaled(n, terms):
    out=[[0]*n for _ in range(n)]
    for coeff,a in terms:
        for i in range(n):
            for j in range(n): out[i][j]+=coeff*a[i][j]
    return out

def eye(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def ones(n): return [[1]*n for _ in range(n)]
def transpose(a): return [list(x) for x in zip(*a)]

def canonical_labels():
    return [(a,b) for a,b in combinations(range(14),2) if b != (a^1)]

def verify(data):
    assert int(data.get("k"))==14
    labels=canonical_labels(); n=len(labels)
    assert n==84
    B=[[0]*n for _ in range(n)]
    for raw in data["edges"]:
        u,v=map(int,raw)
        assert 0<=u<v<n and B[u][v]==0
        B[u][v]=B[v][u]=1
    assert all(B[i][i]==0 for i in range(n))

    X=[[int(i in labels[u]) for u in range(n)] for i in range(14)]
    P=[[int(j==(i^1)) for j in range(14)] for i in range(14)]
    M=mm(transpose(X),X)
    Y=mm(mm(transpose(X),P),X)
    I=eye(n); J=ones(n)

    XB=mm(X,B)
    for i in range(14):
        for u,(a,b) in enumerate(labels):
            rhs=2-int(i in (a,b))-int((i^1) in (a,b))
            assert XB[i][u]==rhs,("XB",i,u,XB[i][u],rhs)
    B2=mm(B,B)
    for u in range(n):
        for v in range(n):
            lhs=B2[u][v]+B[u][v]+M[u][v]
            rhs=12*int(u==v)+2
            assert lhs==rhs,("B polynomial",u,v,lhs,rhs)

    G30=add_scaled(n,[(24,I),(2,J),(-3,M),(-1,Y),(-8,B)])
    G40=add_scaled(n,[(60,I),(-2,J),(-4,M),(1,Y),(15,B)])
    assert mm(G30,G30)==[[56*x for x in row] for row in G30]
    assert mm(G40,G40)==[[105*x for x in row] for row in G40]
    assert all(G30[i][i]==20 for i in range(n))
    assert all(G40[i][i]==50 for i in range(n))
    assert sum(G30[i][i] for i in range(n))==1680
    assert sum(G40[i][i] for i in range(n))==4200

    C=[];D=[]
    for u,v in combinations(range(n),2):
        if not B[u][v]: continue
        if set(labels[u]) & set(labels[v]): C.append((u,v))
        else: D.append((u,v))
    assert len(C)==84 and len(D)==420
    cdeg=[0]*n;ddeg=[0]*n
    for u,v in C: cdeg[u]+=1;cdeg[v]+=1
    for u,v in D: ddeg[u]+=1;ddeg[v]+=1
    assert cdeg==[2]*n and ddeg==[10]*n

    for i in range(14):
        star=[u for u,e in enumerate(labels) if i in e]
        assert len(star)==12
        for u in star:
            assert sum(B[u][v] for v in star)==1

    for i in range(0,14,2):
        left=[u for u,e in enumerate(labels) if i in e]
        right=[u for u,e in enumerate(labels) if i+1 in e]
        for u in left: assert sum(B[u][v] for v in right)==1
        for v in right: assert sum(B[u][v] for u in left)==1

    dset={tuple(sorted(e)) for e in D}
    triangles=[]
    edge_use={e:0 for e in dset}
    per_vertex=[0]*n
    for a,b,c in combinations(range(n),3):
        pairs={(a,b),(a,c),(b,c)}
        if pairs <= dset:
            triangles.append((a,b,c))
            for e in pairs: edge_use[e]+=1
            per_vertex[a]+=1;per_vertex[b]+=1;per_vertex[c]+=1
    assert len(triangles)==140
    assert set(edge_use.values())=={1}
    assert per_vertex==[5]*n

    for u in range(n):
        nbr=[v for v in range(n) if B[u][v]]
        assert len(nbr)==12
        local_deg=[sum(B[v][w] for w in nbr) for v in nbr]
        assert sorted(local_deg)==[0,0]+[1]*10
        c_nbr=[v for v in nbr if set(labels[u]) & set(labels[v])]
        assert len(c_nbr)==2 and all(sum(B[v][w] for w in nbr)==0 for v in c_nbr)

    four_cycle_twice=0
    for u,v in combinations(range(n),2):
        common=sum(B[u][w]&B[v][w] for w in range(n))
        four_cycle_twice+=common*(common-1)//2
    assert four_cycle_twice%2==0 and four_cycle_twice//2==1071

    return {"PASS":True,"method":"independent-projector-structure",
            "reduced_vertices":84,"edges":len(C)+len(D),"C_edges":len(C),
            "D_edges":len(D),"D_triangles":len(triangles),"B_four_cycles":1071,
            "G30":{"rank":30,"identity":"G^2=56G"},
            "G40":{"rank":40,"identity":"G^2=105G"}}

def main():
    ap=argparse.ArgumentParser();ap.add_argument("witness")
    a=ap.parse_args(); data=json.loads(Path(a.witness).read_text())
    print(json.dumps(verify(data),sort_keys=True))
if __name__=="__main__": main()
