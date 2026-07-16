#!/usr/bin/env python3
"""Audit complete corrected s=84 leaf coverage and optionally recheck every proof."""
from __future__ import annotations
import argparse,gzip,hashlib,json,subprocess,tempfile,time
from pathlib import Path

def sha(path):
 h=hashlib.sha256()
 with open(path,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',required=True);ap.add_argument('--cubes',required=True);ap.add_argument('--results',required=True);ap.add_argument('--proofs',required=True);ap.add_argument('--out',required=True);ap.add_argument('--checker');a=ap.parse_args()
 cubes=json.loads(Path(a.cubes).read_text())['cubes'];results=Path(a.results);proofs=Path(a.proofs);base_sha=sha(a.base);cubes_sha=sha(a.cubes);records=[];started=time.time()
 files=sorted(results.glob('leaf_*.json'));assert len(files)==len(cubes),(len(files),len(cubes));seen=set();total_lines=total_gz=0
 with tempfile.TemporaryDirectory() as td:
  td=Path(td)
  for f in files:
   d=json.loads(f.read_text());i=int(d['orbit']);assert i not in seen;seen.add(i);assert d['status']=='VERIFIED_UNSAT';assert d['cube']==[int(x) for x in cubes[i]];assert d['base_sha256']==base_sha and d['cubes_sha256']==cubes_sha
   gz=proofs/f'leaf_{i:04d}.drup.gz';assert gz.exists() and sha(gz)==d['proof_gzip_sha256'];total_lines+=int(d['proof_lines']);total_gz+=gz.stat().st_size
   if a.checker:
    proof=td/'proof.drup';units=td/'units.cnf'
    with gzip.open(gz,'rb') as fi,open(proof,'wb') as fo:
     while True:
      b=fi.read(1<<20)
      if not b:break
      fo.write(b)
    assert sha(proof)==d['proof_sha256'];units.write_text(''.join(f'{int(x)} 0\n' for x in cubes[i]))
    cp=subprocess.run([a.checker,a.base,str(proof),str(units)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=900)
    assert cp.returncode==0 and 's VERIFIED' in cp.stdout,(i,cp.stdout,cp.stderr)
   records.append({'orbit':i,'proof_sha256':d['proof_sha256'],'proof_gzip_sha256':d['proof_gzip_sha256'],'proof_lines':d['proof_lines']})
   if len(records)%100==0:print(json.dumps({'event':'audit','verified':len(records),'total':len(cubes),'elapsed':time.time()-started}),flush=True)
 assert seen==set(range(len(cubes)))
 out={'PASS':True,'problem':'Conway99','branch':'s=84','status':'CERTIFIED_UNSAT','cube_count':len(cubes),'base_sha256':base_sha,'cubes_sha256':cubes_sha,'proof_count':len(records),'total_proof_lines':total_lines,'total_compressed_bytes':total_gz,'proofs_rechecked':bool(a.checker),'elapsed_seconds':time.time()-started,'proofs':records}
 Path(a.out).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='proofs'},indent=2,sort_keys=True))
if __name__=='__main__':main()
