#!/usr/bin/env python3
import itertools
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType as CEnc
import n22_data as d

def weighted_equals_reduced_bdd(cnf,lits,weights,bound,vp,tag='rpb'):
 items=[]
 for lit,w in zip(lits,weights):
  if w<=0:continue
  if w>bound:cnf.append([-lit])
  else:items.append((lit,w))
 items.sort(key=lambda z:(-z[1],abs(z[0])));n=len(items);suffix=[0]*(n+1)
 for i in range(n-1,-1,-1):suffix[i]=suffix[i+1]+items[i][1]
 T=vp.id((tag,'TRUE'));cnf.append([T]);memo={}
 def rec(i,rem):
  if rem<0 or rem>suffix[i]:return -T
  if i==n:return T if rem==0 else -T
  key=(i,rem)
  if key in memo:return memo[key]
  lit,w=items[i];lo=rec(i+1,rem);hi=rec(i+1,rem-w)
  if lo==hi:memo[key]=lo;return lo
  y=vp.id((tag,i,rem));memo[key]=y
  cnf.append([-lit,-hi,y]);cnf.append([lit,-lo,y]);cnf.append([-y,-lit,hi]);cnf.append([-y,lit,lo]);return y
 root=rec(0,bound);cnf.append([root]);return {'items':n,'states':len(memo)}

def base_cnf(vp):
 cnf=CNF()
 for L in d.LINES:
  for a,b,c in itertools.combinations(L,3):cnf.append([-a,-b,-c])
 cnf.extend(CardEnc.equals(list(range(1,len(d.P)+1)),34,vpool=vp,encoding=CEnc.seqcounter).clauses)
 lits=[];ws=[]
 for i,cov in enumerate(d.COVERAGE,1):
  if cov>d.DEN:lits.append(i);ws.append(cov-d.DEN)
 for w,L,nm in d.WL:
  qe=vp.id(('empty',nm));ql=vp.id(('low',nm));cnf.append([qe]+list(L))
  for v in L:cnf.append([-qe,-v])
  for o in range(len(L)):cnf.append([ql]+[L[j] for j in range(len(L)) if j!=o])
  for a,b in itertools.combinations(L,2):cnf.append([-ql,-a,-b])
  cnf.append([-qe,ql]);lits.extend((qe,ql));ws.extend((w,w))
  if w>d.BUD:cnf.extend(CardEnc.equals(list(L),2,vpool=vp,encoding=CEnc.seqcounter).clauses)
  elif 2*w>d.BUD:cnf.append(list(L))
 info=weighted_equals_reduced_bdd(cnf,lits,ws,d.BUD,vp,'slack');return cnf,info

def build_double(top):
 vp=IDPool(start_from=len(d.P)+1);cnf,info=base_cnf(vp)
 for ids in d.BIDS.values():cnf.extend(CardEnc.equals(ids,2,vpool=vp,encoding=CEnc.seqcounter).clauses)
 for i,v in enumerate(d.BIDS['top']):cnf.append([v if (top>>i)&1 else -v])
 for nm in ('left','rb','rr'):
  for m in d.DOUBLES:
   if m>=top:break
   b=[i for i in range(11) if (m>>i)&1];cnf.append([-d.BIDS[nm][b[0]],-d.BIDS[nm][b[1]]])
 cnf.nv=max(cnf.nv,vp.top);return cnf,info

def build_singleton(bit):
 vp=IDPool(start_from=len(d.P)+1);cnf,info=base_cnf(vp)
 cnf.extend(CardEnc.equals(d.BIDS['top'],1,vpool=vp,encoding=CEnc.seqcounter).clauses)
 for nm in ('left','rb','rr'):cnf.extend(CardEnc.equals(d.BIDS[nm],2,vpool=vp,encoding=CEnc.seqcounter).clauses)
 for i,v in enumerate(d.BIDS['top']):cnf.append([v if i==bit else -v])
 cnf.nv=max(cnf.nv,vp.top);return cnf,info
