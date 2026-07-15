#!/usr/bin/env python3
"""Evaluate the 24 previously omitted affine sign towers exactly.

The affine chart fixes z=1, so all 16 sign choices for (u0,u1,u2,u3) are
distinct. Earlier classification incorrectly fixed u0=+1 and therefore omitted
exactly 8 sign points for each of the three known columns.
"""
from __future__ import annotations
import itertools,json,sys
from pathlib import Path
from sage.all import Integer,QQ
sys.path.insert(0,str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc
import sage_kummer_five as k5

GHOST16=[[32,2304,291,34,254],[32,16131,2016,225,38],[28,14396,2631,37,13030],[28,2279,16092,254,5694],[252,28,2047,258,1598],[252,7,292,1793,742],[34,2306,289,226,38],[34,16129,2018,33,254],[30,14398,2629,253,5694],[30,2277,16094,38,13030],[254,30,2045,1794,742],[254,5,294,257,1598],[225,2306,2016,35,254],[225,16129,291,224,38],[5,14398,16092,36,13030],[5,2277,2631,255,5694],[37,30,292,259,1598],[37,5,2047,1792,742],[227,2304,2018,227,38],[227,16131,289,32,254],[7,14396,16094,252,5694],[7,2279,2629,39,13030],[39,28,294,1795,742],[39,7,2045,256,1598]]

def decode(idx,n,r):
 tb=idx%4;v=idx//4;c=[0]*r
 for i in range(r-1,-1,-1):c[i]=v%n;v//=n
 return c,(tb//2,tb%2)
def signed16(c):return c if c<8 else c-16

def torsion_triple(E,p):return [E(0,0),E(-4*p,0)]
def torsion_fifth(E):
 roots=[x for x,m in E.two_division_polynomial().roots(QQ)]
 return [E(roots[0],0),E(roots[1],0)]
def point_from_index(E,gens,tors,idx):
 cs,tb=decode(idx,16,len(gens));P=E(0)
 for c,G in zip(cs,gens):P+=signed16(c)*G
 for b,T in zip(tb,tors):
  if b:P+=T
 return P,[signed16(c) for c in cs],tb

def triple_map(us,inds,E):
 i,j,k=inds;u,v,w=[QQ(us[z]) for z in inds]
 return E(4*(v-u)*(w-u),8*(v-u)*(w-u)*(v+w))
def fifth_map(us,E,p,q,s):
 u0,u1,u2,u3=map(QQ,us)
 if u0==0:return E(0)
 return E(16*p*q*s/(u0*u0),64*p*q*s*(u0*u1*u2*u3)/(u0**4))

def known_exact(factors,E5,p,q,s):
 out=[]
 for t in k5.KNOWN_T:
  mags=[]
  for r in kc.ROWS:
   z=Integer(t)+r*r
   if z<0 or not z.is_square():raise RuntimeError('bad known t')
   mags.append(Integer(z.sqrt()))
  # In the affine chart z=1, all 2^4 signs are distinct.
  for signs in itertools.product([1,-1],repeat=4):
   us=[signs[i]*mags[i] for i in range(4)]
   pts=[triple_map(us,inds,E) for inds,E,_,_ in factors]+[fifth_map(us,E5,p,q,s)]
   out.append({'id':f't={t};signs={signs}','t':int(t),'signs':signs,'points':pts})
 # At infinity z=0, overall projective sign is free, so normalize u0=+1.
 for tail in itertools.product([1,-1],repeat=3):
  signs=(1,)+tail;pts=[]
  for inds,E,a,b in factors:
   i,j,k=inds;pts.append(kc.infinity_image(E,QQ(a),QQ(b),signs[i],signs[j],signs[k]))
  pts.append(k5.quartic_infinity_point(signs,E5,QQ(p),QQ(q),QQ(s)))
  out.append({'id':f'infinity;signs={signs}','t':None,'signs':signs,'points':pts})
 return out

def pj(P):return ['0'] if P.is_zero() else [str(P[0]),str(P[1]),str(P[2])]
def main():
 factors=[];gensall=[];torsall=[]
 for inds in kc.TRIPLES:
  E,p,q=kc.input_curve(inds);gens,r=kc.certified_basis_on_input(E)
  factors.append((inds,E,p,q));gensall.append(gens);torsall.append(torsion_triple(E,p))
 E5,p,q,s=k5.quartic_input_curve();gens5,r5=kc.certified_basis_on_input(E5)
 gensall.append(gens5);torsall.append(torsion_fifth(E5));curves=[x[1] for x in factors]+[E5]
 known=known_exact(factors,E5,p,q,s);report=[]
 for gi,inds in enumerate(GHOST16):
  pts=[];coeff=[];tbs=[]
  for E,gs,ts,idx in zip(curves,gensall,torsall,inds):
   P,c,tb=point_from_index(E,gs,ts,idx);pts.append(P);coeff.append(c);tbs.append(tb)
  matches=[K['id'] for K in known if K['points']==pts]
  ts=[]
  for (tr,E,a,b),P in zip(factors,pts[:4]):
   aa,bb,cc=[kc.ROWS[i] for i in tr];pp=bb*bb-aa*aa;qq=cc*cc-aa*aa
   if P.is_zero():ts.append('infinity')
   elif P[1]==0:ts.append('torsion')
   else:
    u=(16*pp*qq-P[0]**2)/(4*P[1]);ts.append(str(u**2-aa**2))
  P=pts[4]
  ts.append('infinity' if P.is_zero() else str(16*p*q*s/P[0]-kc.ROWS[0]**2))
  report.append({'class':gi,'indices_mod16':inds,'signed_coefficients':coeff,'torsion_bits':tbs,'t_values':ts,'exact_known_matches':matches,'points':[pj(P) for P in pts]})
 out={'class_count':len(report),'known_point_count':len(known),'matched_count':sum(bool(x['exact_known_matches']) for x in report),'unmatched_count':sum(not x['exact_known_matches'] for x in report),'classes':report,'interpretation':'Exact rational equality on all five quotient factors, not reduction signatures.'}
 Path('results').mkdir(exist_ok=True);Path('results/ghost_exact.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'matched':out['matched_count'],'unmatched':out['unmatched_count'],'known':len(known)}))
if __name__=='__main__':main()
