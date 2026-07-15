#!/usr/bin/env python3
"""Sparse lift of the 56 certified mod-8 classes to mod 16."""
from __future__ import annotations
import itertools,json,sys,time
from pathlib import Path
from sage.all import EllipticCurve,GF,Integer,QQ
sys.path.insert(0,str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5
PARENTS=[[0,0,0,2,62],[0,3,3,1,230],[224,16128,2019,226,254],[224,2307,288,33,38],[4,2276,16095,253,13030],[4,14399,2628,38,5694],[36,4,295,1794,1598],[36,31,2044,257,742],[2,2,2,2,230],[2,1,1,1,62],[226,16130,2017,34,38],[226,2305,290,225,254],[6,2278,16093,37,5694],[6,14397,2630,254,13030],[38,6,293,258,742],[38,29,2046,1793,1598],[1,2,3,3,62],[1,1,0,0,230],[33,16130,288,227,254],[33,2305,2019,32,38],[29,2278,2628,252,13030],[29,14397,16095,39,5694],[253,6,2044,1795,1598],[253,29,295,256,742],[3,0,1,3,230],[3,3,2,0,62],[35,16128,290,35,38],[35,2307,2017,224,254],[31,2276,2630,36,5694],[31,14399,16093,255,13030],[255,4,2046,259,742],[255,31,293,1792,1598],[32,2304,291,34,254],[32,16131,2016,225,38],[28,14396,2631,37,13030],[28,2279,16092,254,5694],[252,28,2047,258,1598],[252,7,292,1793,742],[34,2306,289,226,38],[34,16129,2018,33,254],[30,14398,2629,253,5694],[30,2277,16094,38,13030],[254,30,2045,1794,742],[254,5,294,257,1598],[225,2306,2016,35,254],[225,16129,291,224,38],[5,14398,16092,36,13030],[5,2277,2631,255,5694],[37,30,292,259,1598],[37,5,2047,1792,742],[227,2304,2018,227,38],[227,16131,289,32,254],[7,14396,16094,252,5694],[7,2279,2629,39,13030],[39,28,294,1795,742],[39,7,2045,256,1598]]
PRIMES=[31,43,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397]
RANKS=[2,4,4,3,4];OFF=[];z=0
for r in RANKS:OFF.append(z);z+=r
TOTALBITS=z

def quotient_labels(Ep,n):
 pts=list(Ep);H={n*P for P in pts};lab={};i=0
 for P in pts:
  if P in lab:continue
  for Q in H:lab[P+Q]=i
  i+=1
 return lab

def idx_decode(idx,n,r):
 tb=idx%4;v=idx//4;c=[0]*r
 for i in range(r-1,-1,-1):c[i]=v%n;v//=n
 return c,(tb//2,tb%2)
def idx_encode(c,n,tb):
 v=0
 for x in c:v=v*n+x
 return v*4+tb[0]*2+tb[1]
def tbas_triple(E,p):return [E(0,0),E(-4*p,0)]
def tbas_fifth(E):
 rt=[x for x,m in E.two_division_polynomial().roots(QQ)];return [E(rt[0],0),E(rt[1],0)]
def choice(mask,f):return (mask>>OFF[f])&((1<<RANKS[f])-1)
def bits_of(ch,r):return [((ch>>(r-1-i))&1) for i in range(r)]

def make_lifts(E,gens,tors,f):
 r=RANKS[f];allp=[];allidx=[]
 for par in PARENTS:
  c8,tb=idx_decode(par[f],8,r);ps=[];ii=[]
  for ch in range(1<<r):
   b=bits_of(ch,r);c16=[c8[i]+8*b[i] for i in range(r)];P=E(0)
   for a,G in zip(c16,gens):P+=a*G
   for a,T in zip(tb,tors):
    if a:P+=T
   ps.append(P);ii.append(idx_encode(c16,16,tb))
  allp.append(ps);allidx.append(ii)
 return allp,allidx

def main():
 st=time.time();facts=[];LP=[];LI=[]
 for f,inds in enumerate(kc.TRIPLES):
  E,p,q=kc.input_curve(inds);gens,r=kc.certified_basis_on_input(E)
  if r!=RANKS[f]:raise RuntimeError('rank mismatch')
  ps,ii=make_lifts(E,gens,tbas_triple(E,p),f);facts.append((inds,E,p,q));LP.append(ps);LI.append(ii)
 E5,p,q,s=k5.quartic_input_curve();gens,r=kc.certified_basis_on_input(E5)
 ps,ii=make_lifts(E5,gens,tbas_fifth(E5),4);LP.append(ps);LI.append(ii)
 surv=None;progress=[];used=[];BASE=1<<TOTALBITS
 for prime in PRIMES:
  curves0=[x[1] for x in facts]+[E5]
  if any(Integer(E.discriminant())%prime==0 for E in curves0):continue
  if len({int((r*r)%prime) for r in kc.ROWS})<4:continue
  F=GF(prime);curves=[];labs=[]
  for f,(inds,E,a,b) in enumerate(facts):
   Ep=EllipticCurve(F,[F(x) for x in E.a_invariants()]);la=quotient_labels(Ep,16)
   curves.append((inds,Ep,F(a),F(b),la));labs.append([[la[kc.reduce_projective_point(P,Ep,prime)] for P in row] for row in LP[f]])
  E5p=EllipticCurve(F,[F(x) for x in E5.a_invariants()]);la5=quotient_labels(E5p,16)
  labs.append([[la5[kc.reduce_projective_point(P,E5p,prime)] for P in row] for row in LP[4]])
  pp,qq,ss=F(p),F(q),F(s);roots={F(x):[] for x in range(prime)}
  for y in F:roots[y*y].append(y)
  allowed=set()
  for t in F:
   rl=[roots[t+F(r*r)] for r in kc.ROWS]
   if any(not x for x in rl):continue
   for us in itertools.product(*rl):
    zz=[]
    for inds,Ep,a,b,la in curves:
     i,j,k=inds;u,v,w=us[i],us[j],us[k];zz.append(la[Ep(F(4)*(v-u)*(w-u),F(8)*(v-u)*(w-u)*(v+w))])
    zz.append(la5[k5.quartic_local_point(us,E5p,pp,qq,ss)]);allowed.add(tuple(zz))
  for tail in itertools.product([1,-1],repeat=3):
   sg=(1,)+tail;zz=[]
   for inds,Ep,a,b,la in curves:
    i,j,k=inds;zz.append(la[kc.infinity_image(Ep,a,b,sg[i],sg[j],sg[k])])
   zz.append(la5[k5.quartic_infinity_point(sg,E5p,pp,qq,ss)]);allowed.add(tuple(zz))
  if surv is None:
   surv=[]
   for pi in range(len(PARENTS)):
    for mask in range(BASE):
     if tuple(labs[f][pi][choice(mask,f)] for f in range(5)) in allowed:surv.append(pi*BASE+mask)
  else:
   keep=[]
   for code in surv:
    pi,mask=divmod(code,BASE)
    if tuple(labs[f][pi][choice(mask,f)] for f in range(5)) in allowed:keep.append(code)
   surv=keep
  used.append(prime);progress.append({'prime':prime,'local_image_size':len(allowed),'survivors':len(surv)})
  print(f'p={prime} local={len(allowed)} survivors={len(surv)}',flush=True)
 out=[]
 for code in surv:
  pi,mask=divmod(code,BASE);out.append([LI[f][pi][choice(mask,f)] for f in range(5)])
 data={'rows':[int(x) for x in kc.ROWS],'starting_mod8_classes':len(PARENTS),'initial_mod16_lifts':len(PARENTS)*BASE,'used_primes':used,'progress':progress,'survivor_count':len(out),'survivor_indices':out,'elapsed_seconds':round(time.time()-st,3),'soundness':'Complete local images in all five elliptic quotients modulo 16.'}
 Path('results').mkdir(exist_ok=True);Path('results/kummer_mod16.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');print(json.dumps({'survivors':len(out),'elapsed':data['elapsed_seconds']}))
if __name__=='__main__':main()
