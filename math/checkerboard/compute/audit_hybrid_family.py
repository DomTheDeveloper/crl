#!/usr/bin/env python3
"""Audit a hybrid exact family partition of fixed-left and fixed-(left,bottom) scopes."""
import argparse, hashlib, json
from pathlib import Path
import n22_data as d

ap=argparse.ArgumentParser()
ap.add_argument('--top',type=int,required=True)
ap.add_argument('--direct-dir',required=True)
ap.add_argument('--split-root',required=True)
ap.add_argument('--split-lefts',required=True,help='comma-separated left masks')
ap.add_argument('--out',required=True)
a=ap.parse_args();top=a.top;direct=Path(a.direct_dir);splitroot=Path(a.split_root)
splits={int(x) for x in a.split_lefts.split(',') if x.strip()}
allm=[m for m in d.DOUBLES if m>=top];lefts=[m for m in allm if (m&1)==(top&1)]
errors=[];records=[]
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1<<20),b''):h.update(block)
 return h.hexdigest()
def read_result(path):
 try:rows=[json.loads(x) for x in path.read_text().splitlines() if x.strip()]
 except Exception as exc:return None,f'parse:{exc}'
 if any(r.get('status')=='SAT' or r.get('event')=='WITNESS' for r in rows):return None,'SAT/witness'
 if not rows or rows[-1].get('status')!='UNSAT':return None,'missing final UNSAT'
 return rows[-1],None
for left in lefts:
 if left in splits:
  for bottom in allm:
   path=splitroot/f'l{left}'/f'rb{bottom}.log';rec,err=read_result(path)
   if err:errors.append(f'left {left} bottom {bottom}: {err}')
   records.append({'scope':'bottom','left':left,'bottom':bottom,'file':str(path),'sha256':sha(path) if path.exists() else None,'result':rec,'error':err})
 else:
  path=direct/f'l{left}.log';rec,err=read_result(path)
  if err:errors.append(f'left {left}: {err}')
  records.append({'scope':'left','left':left,'file':str(path),'sha256':sha(path) if path.exists() else None,'result':rec,'error':err})
def canonical(t,l,b,r):
 q=(t,l,b,r);return q==min({q,(l,t,r,b),(b,r,t,l),(r,b,l,t)})
owner_counts={};orbit_count=0
for left in lefts:
 for bottom in allm:
  for right in allm:
   if (right&1)!=(bottom&1) or not canonical(top,left,bottom,right):continue
   orbit_count+=1
   owner=('bottom',left,bottom) if left in splits else ('left',left)
   owner_counts[owner]=owner_counts.get(owner,0)+1
expected={('left',left) for left in lefts if left not in splits}|{('bottom',left,bottom) for left in splits for bottom in allm}
missing=sorted(expected-set(owner_counts),key=str);extra=sorted(set(owner_counts)-expected,key=str)
if missing:errors.append(f'missing owners {missing}')
if extra:errors.append(f'extra owners {extra}')
report={'target':34,'top':top,'left_count':len(lefts),'bottom_count':len(allm),'split_lefts':sorted(splits),'direct_left_scopes':len(lefts)-len(splits),'split_bottom_scopes':len(splits)*len(allm),'canonical_boundary_orbits':orbit_count,'owner_count':len(owner_counts),'missing_owners':missing,'extra_owners':extra,'records':records,'errors':errors,'PASS':not errors}
Path(a.out).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({key:report[key] for key in ('top','direct_left_scopes','split_bottom_scopes','canonical_boundary_orbits','owner_count','errors','PASS')},indent=2))
raise SystemExit(1 if errors else 0)
