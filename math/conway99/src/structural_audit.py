#!/usr/bin/env python3
"""Executable audit of exact structural consequences of SRG(99,14,1,2).

This script proves no existence/nonexistence claim by itself. It mechanically
checks the finite counting and linear-algebra calculations used by the search.
"""
from __future__ import annotations
import json
from collections import Counter
from itertools import combinations
from model import make_root_model


def matmul(a, b):
    return [[sum(x*y for x,y in zip(row, col)) for col in zip(*b)] for row in a]

def transpose(a):
    return [list(col) for col in zip(*a)]

def perfect_matchings(vertices):
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for j in range(1, len(vertices)):
        b = vertices[j]
        rest = vertices[1:j] + vertices[j+1:]
        for tail in perfect_matchings(rest):
            yield ((a,b),) + tail

def cycle_type_of_two_matchings(fixed, other, n=12):
    adj = [[] for _ in range(n)]
    for matching in (fixed, other):
        for a,b in matching:
            adj[a].append(b); adj[b].append(a)
    seen=set(); sizes=[]
    for s in range(n):
        if s in seen: continue
        stack=[s]; seen.add(s); size=0
        while stack:
            x=stack.pop(); size+=1
            for y in adj[x]:
                if y not in seen:
                    seen.add(y); stack.append(y)
        sizes.append(size)
    assert all(len(v)==2 for v in adj)
    return tuple(sorted(sizes, reverse=True))

def audit():
    rm=make_root_model(14)
    assert rm.m==84 and rm.v==99
    X=[[int(i in e) for e in rm.labels] for i in range(14)]
    P=[[int(j==(i^1)) for j in range(14)] for i in range(14)]
    XXt=matmul(X,transpose(X))
    expected=[[11*int(i==j)+1-int(j==(i^1)) for j in range(14)] for i in range(14)]
    assert XXt==expected

    intersecting=sum(1 for u,v in combinations(range(84),2) if rm.intersection(u,v)==1)
    disjoint=sum(1 for u,v in combinations(range(84),2) if rm.intersection(u,v)==0)
    assert intersecting==924 and disjoint==2562 and intersecting+disjoint==3486
    disjoint_triples=sum(1 for a,b,c in combinations(range(84),3)
                         if len(set(rm.labels[a]+rm.labels[b]+rm.labels[c]))==6)
    assert disjoint_triples==35560

    fixed=tuple((i,i+1) for i in range(0,12,2))
    types=Counter(cycle_type_of_two_matchings(fixed,m) for m in perfect_matchings(range(12)))
    expected_types={
      (12,):3840,(10,2):2304,(8,4):1440,(8,2,2):720,(6,6):640,
      (6,4,2):960,(6,2,2,2):160,(4,4,4):120,(4,4,2,2):180,
      (4,2,2,2,2):30,(2,2,2,2,2,2):1,
    }
    assert dict(types)==expected_types and sum(types.values())==10395

    spaces=[
      ("ones",1,12,24,24,84),
      ("pair_constant",6,-2,10,10,0),
      ("pair_difference",7,0,12,-12,0),
      ("kernel_eigen_3",40,3,0,0,0),
      ("kernel_eigen_minus4",30,-4,0,0,0),
    ]
    g30=[];g40=[]
    for name,mult,b,m,y,j in spaces:
        a30=24+2*j-3*m-y-8*b
        a40=60-2*j-4*m+y+15*b
        g30.append((name,mult,a30)); g40.append((name,mult,a40))
    assert [x[2] for x in g30]==[0,0,0,0,56]
    assert [x[2] for x in g40]==[0,0,0,105,0]
    assert sum(mult for _,mult,eig in g30 if eig != 0) == 30
    assert sum(mult for _,mult,eig in g40 if eig != 0) == 40
    assert sum(mult*eig for _,mult,eig in g30)==1680
    assert sum(mult*eig for _,mult,eig in g40)==4200

    c_edges=84; d_edges=420; d_triangles=140
    disjoint_nonedges=disjoint-d_edges
    b_four_cycles=disjoint_nonedges//2
    assert disjoint_nonedges==2142 and b_four_cycles==1071
    full_triangles=7+c_edges+d_triangles
    assert full_triangles==231

    q_spectrum={18:1,7:54,0:44,-3:132}
    assert sum(q_spectrum.values())==231
    assert sum(e*m for e,m in q_spectrum.items())==0
    assert sum(e*e*m for e,m in q_spectrum.items())==231*18

    radius_one=[]
    for t in range(13):
        row=(32-t,144+3*t,36-3*t,t)
        assert sum(row)==212
        assert sum(j*row[j] for j in range(4))==216
        assert row[2]+3*row[3]==36
        assert min(row)>=0
        radius_one.append(row)

    return {
      "PASS":True,
      "root_reduction":{"v":99,"k":14,"reduced_vertices":84},
      "label_pair_counts":{"intersecting":intersecting,"disjoint":disjoint},
      "hypergraph_candidates":{"transition_edges":intersecting,"disjoint_triples":disjoint_triples},
      "reduced_spectrum":{"12":1,"-2":6,"0":7,"3":40,"-4":30},
      "reduced_structure":{"C_edges":c_edges,"D_edges":d_edges,"D_triangles":d_triangles,
                           "B_four_cycles":b_four_cycles},
      "full_triangle_count":full_triangles,
      "triangle_graph_spectrum":{str(k):v for k,v in q_spectrum.items()},
      "projectors":{"G30":{"rank":30,"nonzero_eigenvalue":56,"trace":1680,"diagonal":20},
                    "G40":{"rank":40,"nonzero_eigenvalue":105,"trace":4200,"diagonal":50}},
      "adjacent_pair_local_types":{"count":11,"total_matchings":10395,
        "cycle_type_counts":{"+".join(map(str,k)):v for k,v in sorted(types.items())}},
      "triangle_graph_radius_one_profiles":[list(x) for x in radius_one],
    }

def main():
    print(json.dumps(audit(),indent=2,sort_keys=True))
if __name__=="__main__": main()
