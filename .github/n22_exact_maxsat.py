#!/usr/bin/env python3
"""Direct exact MaxSAT optimization of the n=22 monochromatic no-three problem."""
import itertools,json,math,time
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
N=22
P=[(x,y) for x in range(N) for y in range(N) if (x+y)%2==0]
def key(p,q):
 x1,y1=p;x2,y2=q;a=y2-y1;b=x1-x2;c=-(a*x1+b*y1)
 g=math.gcd(math.gcd(abs(a),abs(b)),abs(c));a//=g;b//=g;c//=g
 if a<0 or (a==0 and b<0):a,b,c=-a,-b,-c
 return a,b,c
D={}
for i,p in enumerate(P):
 for j in range(i+1,len(P)):
  s=D.setdefault(key(p,P[j]),set());s.add(i+1);s.add(j+1)
LINES=sorted(tuple(sorted(s)) for s in D.values() if len(s)>=3)
assert len(P)==242 and len(LINES)==2455
w=WCNF()
for L in LINES:
 for a,b,c in itertools.combinations(L,3):w.append([-a,-b,-c])
for i in range(1,len(P)+1):w.append([i],weight=1)
print(json.dumps({'event':'built','points':len(P),'lines':len(LINES),'hard':len(w.hard),'soft':len(w.soft)}),flush=True)
t=time.time()
with RC2(w,solver='g4',adapt=True,exhaust=True,incr=False,minz=True,trim=10,verbose=1) as r:
 model=r.compute();selected=[P[i-1] for i in model if 1<=i<=len(P)]
 rec={'event':'result','status':'OPTIMUM','maximum':len(selected),'cost':r.cost,'seconds':time.time()-t,'points':selected}
 print(json.dumps(rec),flush=True)
 raise SystemExit(2 if len(selected)>=34 else (0 if len(selected)==33 else 3))
