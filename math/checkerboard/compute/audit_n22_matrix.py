#!/usr/bin/env python3
"""Independent coverage audit for downloaded GitHub Actions manifests."""
import argparse,glob,json,sys
from pathlib import Path
import n22_data as c
ap=argparse.ArgumentParser();ap.add_argument('--root',default='artifacts');ap.add_argument('--shards',type=int,default=4);ap.add_argument('--out',default='n22_global_audit.json');a=ap.parse_args()
errors=[];tot={'double_shards':0,'double_lefts':0,'double_rb_direct':0,'double_leaves':0,'singleton_bits':0,'singleton_lefts':0,'singleton_rb_direct':0,'singleton_leaves':0,'witnesses':0}
def rows_for(pattern):
 fs=glob.glob(str(Path(a.root)/'**'/pattern),recursive=True);rows=[]
 for fn in fs:
  for n,line in enumerate(Path(fn).read_text().splitlines(),1):
   try:rows.append((fn,n,json.loads(line)))
   except Exception as e:errors.append(f'{fn}:{n}: invalid JSON: {e}')
 return fs,rows
for top in c.DOUBLES:
 allm=[m for m in c.DOUBLES if m>=top];lefts_all=[m for m in allm if (m&1)==(top&1)];covered=[]
 for shard in range(a.shards):
  fs,rows=rows_for(f'double_{top}_{shard}.jsonl')
  if len(fs)!=1:errors.append(f'top {top} shard {shard}: expected one manifest, found {fs}');continue
  R=[r for _,_,r in rows]
  if any(r.get('event')=='WITNESS' or r.get('status')=='SAT' for r in R):errors.append(f'top {top} shard {shard}: witness/SAT');tot['witnesses']+=1
  ss=[r for r in R if r.get('event')=='shard_summary']
  if len(ss)!=1 or not ss[0].get('closed'):errors.append(f'top {top} shard {shard}: bad summary {ss}')
  assigned=[m for i,m in enumerate(lefts_all) if i%a.shards==shard]
  if ss and ss[0].get('assigned_lefts')!=assigned:errors.append(f'top {top} shard {shard}: assigned-left mismatch')
  covered.extend(assigned);tot['double_shards']+=1
  direct_left={r['left'] for r in R if r.get('event')=='left' and r.get('status')=='UNSAT'}
  direct_rb={(r['left'],r['rb']) for r in R if r.get('event')=='rb' and r.get('status')=='UNSAT'}
  leaves={(r['left'],r['rb'],r['rr']) for r in R if r.get('event')=='leaf' and r.get('status')=='UNSAT'}
  for left in assigned:
   if left in direct_left:continue
   for rb in allm:
    if (left,rb) in direct_rb:continue
    required=[]
    for rr in allm:
     if (rr&1)!=(rb&1):continue
     if left==top and rr<rb:continue
     if rb==top and rr<left:continue
     if rr==top and rb<left:continue
     required.append(rr)
    miss=[rr for rr in required if (left,rb,rr) not in leaves]
    if miss:errors.append(f'top {top} shard {shard} left {left} rb {rb}: missing {miss}')
  tot['double_lefts']+=len(assigned);tot['double_rb_direct']+=len(direct_rb);tot['double_leaves']+=len(leaves)
 if sorted(covered)!=lefts_all:errors.append(f'top {top}: shard union mismatch')
for bit in range(11):
 fs,rows=rows_for(f'singleton_{bit}.jsonl')
 if len(fs)!=1:errors.append(f'singleton bit {bit}: expected one manifest, found {fs}');continue
 R=[r for _,_,r in rows]
 if any(r.get('event')=='WITNESS' or r.get('status')=='SAT' for r in R):errors.append(f'singleton bit {bit}: witness/SAT');tot['witnesses']+=1
 ss=[r for r in R if r.get('event')=='summary']
 if len(ss)!=1 or not ss[0].get('closed'):errors.append(f'singleton bit {bit}: bad summary {ss}')
 corner=1 if bit==0 else 0;lefts=[m for m in c.DOUBLES if (m&1)==corner];rbs=list(c.DOUBLES)
 dl={r['left'] for r in R if r.get('event')=='left' and r.get('status')=='UNSAT'};dr={(r['left'],r['rb']) for r in R if r.get('event')=='rb' and r.get('status')=='UNSAT'};lv={(r['left'],r['rb'],r['rr']) for r in R if r.get('event')=='leaf' and r.get('status')=='UNSAT'}
 for left in lefts:
  if left in dl:continue
  for rb in rbs:
   if (left,rb) in dr:continue
   req=[rr for rr in rbs if (rr&1)==(rb&1)];miss=[rr for rr in req if (left,rb,rr) not in lv]
   if miss:errors.append(f'singleton bit {bit} left {left} rb {rb}: missing {miss}')
 tot['singleton_bits']+=1;tot['singleton_lefts']+=len(lefts);tot['singleton_rb_direct']+=len(dr);tot['singleton_leaves']+=len(lv)
report={'target':34,'singleton_closed':tot['singleton_bits']==11,'double_top_closed':55 if not any(e.startswith('top ') for e in errors) else None,'witnesses':tot['witnesses'],'unknown_unresolved':len(errors),'totals':tot,'errors':errors,'PASS':not errors}
Path(a.out).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2));sys.exit(1 if errors else 0)
