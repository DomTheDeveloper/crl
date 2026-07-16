#!/usr/bin/env python3
"""Enumerate the 1,712 exhaustive seed-star cubes in the corrected s=84 branch.

After fixing the seed label, its ten disjoint fibers are the ten edges of K5.
The five triangles through the seed pair these fibers according to a perfect
matching of the Petersen graph KG(5,2). S5 is transitive on the six Petersen
perfect matchings, so one matching is fixed. Its signed stabilizer has effective
order 20*2^5=640 on the 2^20 sign assignments. This program enumerates every
orbit exactly and emits the corresponding fifteen positive SAT literals.
"""
from __future__ import annotations
import argparse, json
from collections import deque
from itertools import combinations, permutations
from pathlib import Path
from s84_cover_sat import INDEX, key, build
V=range(5);EDGES=tuple(combinations(V,2));EIDX={e:i for i,e in enumerate(EDGES)}
def petersen_perfect_matchings():
    adj={e:{f for f in EDGES if set(e).isdisjoint(f)} for e in EDGES};ans=[]
    def rec(rem,pairs):
        if not rem:ans.append(tuple(sorted(tuple(sorted((a,b))) for a,b in pairs)));return
        a=min(rem)
        for b in sorted(adj[a]&rem):rec(rem-{a,b},pairs+[(a,b)])
    rec(set(EDGES),[]);return sorted(set(ans))
MATCHINGS=petersen_perfect_matchings();M=MATCHINGS[0]
def perm_edge(e,p):
    a,b=p[e[0]],p[e[1]];return (a,b) if a<b else (b,a)
def perm_matching(m,p):return tuple(sorted(tuple(sorted((perm_edge(a,p),perm_edge(b,p)))) for a,b in m))
PSTAB=[p for p in permutations(V) if perm_matching(M,p)==M]
assert len(MATCHINGS)==6 and len(PSTAB)==20
def transform_state(s,p,flip):
    out=0
    for ei,(a,b) in enumerate(EDGES):
        sa=(s>>(2*ei))&1;sb=(s>>(2*ei+1))&1;aa=p[a];bb=p[b]
        sa^=(flip>>aa)&1;sb^=(flip>>bb)&1
        if aa<bb:oi=EIDX[(aa,bb)];x,y=sa,sb
        else:oi=EIDX[(bb,aa)];x,y=sb,sa
        out|=x<<(2*oi);out|=y<<(2*oi+1)
    return out
def compose(g,h):
    pg,fg=g;ph,fh=h;p=tuple(pg[ph[i]] for i in V);f=0
    for i in V:
        j=pg[ph[i]];f|=((((fh>>ph[i])&1)^((fg>>j)&1))<<j)
    return p,f
def closure(gens):
    ident=(tuple(V),0);seen={ident};q=deque([ident])
    while q:
        x=q.popleft()
        for g in gens:
            y=compose(g,x)
            if y not in seen:seen.add(y);q.append(y)
    return seen
def choose_generators():
    gens=[(tuple(V),1<<i) for i in V];cl=closure(gens)
    for p in PSTAB:
        g=(p,0)
        if g not in cl:gens.append(g);cl=closure(gens)
        if len(cl)==640:break
    assert len(cl)==640;return gens,cl
GENS,GROUP=choose_generators()
def orbit_representatives():
    seen=bytearray(1<<20);reps=[];sizes=[]
    for s in range(1<<20):
        if seen[s]:continue
        q=[s];seen[s]=1;orb=[]
        while q:
            x=q.pop();orb.append(x)
            for p,f in GENS:
                y=transform_state(x,p,f)
                if not seen[y]:seen[y]=1;q.append(y)
        reps.append(min(orb));sizes.append(len(orb))
    assert sum(sizes)==1<<20 and len(reps)==1712;return reps,sizes
def selected_labels(state):
    out={}
    for ei,(a,b) in enumerate(EDGES):
        sa=(state>>(2*ei))&1;sb=(state>>(2*ei+1))&1
        out[(a,b)]=INDEX[tuple(sorted((2*(a+2)+sa,2*(b+2)+sb)))]
    return out
def cube_for_state(state,d):
    seed=INDEX[(0,2)];sel=selected_labels(state)
    lits=[d[key(seed,sel[e])] for e in EDGES]+[d[key(sel[e],sel[f])] for e,f in M]
    assert len(lits)==15 and len(set(lits))==15;return sorted(lits)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args()
    reps,sizes=orbit_representatives();cnf,d,_=build(False);cubes=[cube_for_state(s,d) for s in reps]
    data={'PASS':True,'raw_assignments':1<<20,'petersen_matchings':6,'permutation_stabilizer_size':20,
          'effective_signed_group_size':640,'generator_count':len(GENS),'orbit_count':len(reps),
          'orbit_size_histogram':{str(k):sizes.count(k) for k in sorted(set(sizes))},
          'representatives':reps,'cubes':cubes,'base_variables':cnf.nv,'base_clauses':len(cnf.clauses)}
    Path(a.out).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('representatives','cubes')},indent=2,sort_keys=True))
if __name__=='__main__':main()
