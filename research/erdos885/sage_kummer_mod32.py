#!/usr/bin/env python3
"""Sparse lift of the 56 certified mod-16 classes to mod 32."""
from __future__ import annotations
import itertools,json,sys,time
from pathlib import Path
from sage.all import EllipticCurve,GF,Integer,QQ
sys.path.insert(0,str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5
PARENTS=[[0, 0, 0, 2, 126], [0, 3, 3, 1, 966], [960, 261120, 16323, 962, 1022], [960, 17411, 1088, 65, 70], [4, 17348, 261055, 1021, 232390], [4, 245887, 18564, 70, 47230], [68, 4, 1095, 15362, 14462], [68, 63, 16380, 1025, 3014], [2, 2, 2, 2, 966], [2, 1, 1, 1, 126], [962, 261122, 16321, 66, 70], [962, 17409, 1090, 961, 1022], [6, 17350, 261053, 69, 47230], [6, 245885, 18566, 1022, 232390], [70, 6, 1093, 1026, 3014], [70, 61, 16382, 15361, 14462], [1, 2, 3, 3, 126], [1, 1, 0, 0, 966], [65, 261122, 1088, 963, 1022], [65, 17409, 16323, 64, 70], [61, 17350, 18564, 1020, 232390], [61, 245885, 261055, 71, 47230], [1021, 6, 16380, 15363, 14462], [1021, 61, 1095, 1024, 3014], [3, 0, 1, 3, 966], [3, 3, 2, 0, 126], [67, 261120, 1090, 67, 70], [67, 17411, 16321, 960, 1022], [63, 17348, 18566, 68, 47230], [63, 245887, 261053, 1023, 232390], [1023, 4, 16382, 1027, 3014], [1023, 63, 1093, 15360, 14462], [64, 17408, 1091, 66, 1022], [64, 261123, 16320, 961, 70], [60, 245884, 18567, 69, 232390], [60, 17351, 261052, 1022, 47230], [1020, 60, 16383, 1026, 14462], [1020, 7, 1092, 15361, 3014], [66, 17410, 1089, 962, 70], [66, 261121, 16322, 65, 1022], [62, 245886, 18565, 1021, 47230], [62, 17349, 261054, 70, 232390], [1022, 62, 16381, 15362, 3014], [1022, 5, 1094, 1025, 14462], [961, 17410, 16320, 67, 1022], [961, 261121, 1091, 960, 70], [5, 245886, 261052, 68, 232390], [5, 17349, 18567, 1023, 47230], [69, 62, 1092, 1027, 14462], [69, 5, 16383, 15360, 3014], [963, 17408, 16322, 963, 70], [963, 261123, 1089, 64, 1022], [7, 245884, 261054, 1020, 47230], [7, 17351, 18565, 71, 232390], [71, 60, 1094, 15363, 3014], [71, 7, 16381, 1024, 14462]]
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
  c16,tb=idx_decode(par[f],16,r);ps=[];ii=[]
  for ch in range(1<<r):
   b=bits_of(ch,r);c32=[c16[i]+16*b[i] for i in range(r)];P=E(0)
   for a,G in zip(c32,gens):P+=a*G
   for a,T in zip(tb,tors):
    if a:P+=T
   ps.append(P);ii.append(idx_encode(c32,32,tb))
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
   Ep=EllipticCurve(F,[F(x) for x in E.a_invariants()]);la=quotient_labels(Ep,32)
   curves.append((inds,Ep,F(a),F(b),la));labs.append([[la[kc.reduce_projective_point(P,Ep,prime)] for P in row] for row in LP[f]])
  E5p=EllipticCurve(F,[F(x) for x in E5.a_invariants()]);la5=quotient_labels(E5p,32)
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
 data={'rows':[int(x) for x in kc.ROWS],'starting_mod16_classes':len(PARENTS),'initial_mod32_lifts':len(PARENTS)*BASE,'used_primes':used,'progress':progress,'survivor_count':len(out),'survivor_indices':out,'elapsed_seconds':round(time.time()-st,3),'soundness':'Complete local images in all five elliptic quotients modulo 32.'}
 Path('results').mkdir(exist_ok=True);Path('results/kummer_mod32.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');print(json.dumps({'survivors':len(out),'elapsed':data['elapsed_seconds']}))
if __name__=='__main__':main()
