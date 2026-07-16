#!/usr/bin/env python3
"""Exhaustive symmetry audit for the exact s=84 cover encoding."""
from __future__ import annotations
import json
from itertools import combinations, permutations, product

K=14
SEED=(0,2)
def mate(i):return i^1
def canon(e):return tuple(sorted(e))
LABELS={canon(e) for e in combinations(range(K),2) if mate(e[0])!=e[1]}
def y(e,f):return sum(1 for a in e for b in f if mate(a)==b)
def valid_triangle(t):
    a,b,c=t
    return all(set(u).isdisjoint(v) and y(u,v)==0
               for u,v in ((a,b),(a,c),(b,c)))

def stabilizer_maps():
    for edge_perm in permutations(range(7)):
        for flips in product((0,1),repeat=7):
            g=tuple(2*edge_perm[x//2]+((x%2)^flips[x//2]) for x in range(K))
            if {g[0],g[2]}==set(SEED):yield g

def act(triangle,g):
    return tuple(sorted(canon((g[a],g[b])) for a,b in triangle))

def audit():
    candidates=[]
    for b,c in combinations(sorted(LABELS-{SEED}),2):
        t=tuple(sorted((SEED,b,c)))
        if valid_triangle(t):candidates.append(t)
    maps=list(stabilizer_maps())
    assert len(maps)==7680 and len(candidates)==240
    orbit={act(candidates[0],g) for g in maps}
    assert orbit==set(candidates)
    representative=min(orbit)
    return {"PASS":True,"stabilizer_size":len(maps),
      "seed_triangle_candidates":len(candidates),"orbit_count":1,
      "representative":[list(x) for x in representative]}

def main():print(json.dumps(audit(),indent=2,sort_keys=True))
if __name__=="__main__":main()
