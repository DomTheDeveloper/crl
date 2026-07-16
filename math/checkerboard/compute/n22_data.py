#!/usr/bin/env python3
"""Exact n=22 checkerboard geometry and rational dual certificate data."""
import math
N=22;DEN=187;OBJ=6470;BUD=OBJ-34*DEN
A=[63,48,35,24,15,8,3,0,0,0,0]
B=[0,0,0,22,40,54,67,80,92,100,104]
C=[117,115,109,99,85,72,60,44,24,0,0]
P=[(x,y) for x in range(N) for y in range(N) if (x+y)%2==0]
idx={p:i+1 for i,p in enumerate(P)}
def line_key(p,q):
 x1,y1=p;x2,y2=q;a=y2-y1;b=x1-x2;c=-(a*x1+b*y1)
 g=math.gcd(math.gcd(abs(a),abs(b)),abs(c));a//=g;b//=g;c//=g
 if a<0 or (a==0 and b<0):a,b,c=-a,-b,-c
 return a,b,c
d={}
for i,p in enumerate(P):
 for j in range(i+1,len(P)):
  s=d.setdefault(line_key(p,P[j]),set());s.add(i+1);s.add(j+1)
LINES=sorted(tuple(sorted(s)) for s in d.values() if len(s)>=3)
WL=[]
for x0 in range(N):
 w=A[min(x0,N-1-x0)];L=[idx[(x0,y)] for y in range(N) if (x0+y)%2==0]
 if w:WL.append((w,L,f'x{x0}'))
for y0 in range(N):
 w=A[min(y0,N-1-y0)];L=[idx[(x,y0)] for x in range(N) if (x+y0)%2==0]
 if w:WL.append((w,L,f'y{y0}'))
for sm in range(0,2*N-1,2):
 w=B[min(sm//2,N-1-sm//2)];L=[idx[(x,sm-x)] for x in range(N) if 0<=sm-x<N]
 if w:WL.append((w,L,f's{sm}'))
for dd in range(-(N-2),N-1,2):
 w=C[abs(dd)//2];L=[idx[(x,x-dd)] for x in range(N) if 0<=x-dd<N]
 if w:WL.append((w,L,f'd{dd}'))
COVERAGE=[sum(w for w,L,_ in WL if i+1 in L) for i in range(len(P))]
assert len(P)==242 and len(LINES)==2455 and len(WL)==61 and min(COVERAGE)>=DEN
assert 2*sum(w for w,_,_ in WL)==OBJ and BUD==112
BPOINTS={'top':[(0,2*i) for i in range(11)],'left':[(2*i,0) for i in range(11)],
 'rb':[(21,21-2*i) for i in range(11)],'rr':[(21-2*i,21) for i in range(11)]}
BIDS={k:[idx[p] for p in ps] for k,ps in BPOINTS.items()}
DOUBLES=sorted((1<<i)|(1<<j) for i in range(11) for j in range(i+1,11))
