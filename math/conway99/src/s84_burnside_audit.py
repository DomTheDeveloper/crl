#!/usr/bin/env python3
"""Independent Burnside audit of the 1,712 corrected s=84 seed-star orbits."""
from itertools import combinations,permutations
import json
V=range(5);EDGES=tuple(combinations(V,2));EIDX={e:i for i,e in enumerate(EDGES)}
def pe(e,p):
    a,b=p[e[0]],p[e[1]];return (a,b) if a<b else (b,a)
def pms():
    adj={e:{f for f in EDGES if set(e).isdisjoint(f)} for e in EDGES};ans=[]
    def rec(rem,ps):
        if not rem:ans.append(tuple(sorted(tuple(sorted(x)) for x in ps)));return
        a=min(rem)
        for b in sorted(adj[a]&rem):rec(rem-{a,b},ps+[(a,b)])
    rec(set(EDGES),[]);return sorted(set(ans))
MS=pms();M=MS[0]
def pm(m,p):return tuple(sorted(tuple(sorted((pe(a,p),pe(b,p)))) for a,b in m))
P=[p for p in permutations(V) if pm(M,p)==M]
assert len(MS)==6 and len(P)==20
def bit_action(p,flip):
    dest=[None]*20;xor=[None]*20
    for ei,(a,b) in enumerate(EDGES):
        for pos,g in enumerate((a,b)):
            gg=p[g];other=p[b if pos==0 else a];e=(gg,other) if gg<other else (other,gg);oi=EIDX[e]
            dest[2*ei+pos]=2*oi+(0 if gg<other else 1);xor[2*ei+pos]=(flip>>gg)&1
    return dest,xor
def fixed_count(p,flip):
    d,c=bit_action(p,flip);seen=[False]*20;cycles=0
    for i in range(20):
        if seen[i]:continue
        cycles+=1;j=i;par=0
        while not seen[j]:seen[j]=True;par^=c[j];j=d[j]
        assert j==i
        if par:return 0
    return 1<<cycles
def audit():
    total=0;hist={}
    for p in P:
        for f in range(32):
            n=fixed_count(p,f);total+=n;hist[n]=hist.get(n,0)+1
    assert total==1095680 and total//640==1712
    return {'PASS':True,'petersen_perfect_matchings':6,'matching_stabilizer':20,'signed_group_size':640,
            'burnside_fixed_sum':total,'orbit_count':total//640,
            'fixed_count_histogram':{str(k):v for k,v in sorted(hist.items())}}
if __name__=='__main__':print(json.dumps(audit(),indent=2,sort_keys=True))
