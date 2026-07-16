#!/usr/bin/env python3
"""Solve and independently check one deterministic shard of corrected s=84 cubes."""
from __future__ import annotations
import argparse,gzip,hashlib,json,subprocess,time
from pathlib import Path
from pysat.formula import CNF
from pysat.solvers import Solver

def sha(path):
 h=hashlib.sha256()
 with open(path,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def atomic_json(path,data):
 p=Path(path);tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');tmp.replace(p)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',required=True);ap.add_argument('--cubes',required=True);ap.add_argument('--checker',required=True);ap.add_argument('--out',required=True);ap.add_argument('--shard-index',type=int,required=True);ap.add_argument('--shard-count',type=int,required=True);ap.add_argument('--solver',default='glucose4');a=ap.parse_args()
 out=Path(a.out);(out/'results').mkdir(parents=True,exist_ok=True);(out/'proofs').mkdir(parents=True,exist_ok=True);work=out/'work';work.mkdir(exist_ok=True)
 data=json.loads(Path(a.cubes).read_text());cubes=data['cubes'];ids=[i for i in range(len(cubes)) if i%a.shard_count==a.shard_index]
 formula=CNF(from_file=a.base);base_sha=sha(a.base);cubes_sha=sha(a.cubes);started=time.time();records=[]
 for pos,i in enumerate(ids,1):
  cube=[int(x) for x in cubes[i]];units=work/f'leaf_{i:04d}.units';proof=work/f'leaf_{i:04d}.drup';units.write_text(''.join(f'{x} 0\n' for x in cube))
  t=time.time()
  with Solver(name=a.solver,bootstrap_with=formula.clauses,with_proof=True) as solver:
   for x in cube:solver.add_clause([x])
   sat=solver.solve();solve_seconds=time.time()-t
   if sat:
    model=solver.get_model();atomic_json(out/'results'/f'leaf_{i:04d}.json',{'orbit':i,'status':'SAT','cube':cube,'model':model,'solve_seconds':solve_seconds});raise RuntimeError(f'SAT leaf {i}')
   trace=solver.get_proof()
  if not trace:raise RuntimeError(f'UNSAT leaf {i} returned no proof')
  proof.write_text('\n'.join(trace)+'\n');proof_sha=sha(proof);tc=time.time()
  cp=subprocess.run([a.checker,a.base,str(proof),str(units)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=900);check_seconds=time.time()-tc
  if cp.returncode or 's VERIFIED' not in cp.stdout:
   atomic_json(out/'results'/f'leaf_{i:04d}.json',{'orbit':i,'status':'CHECK_FAILED','cube':cube,'proof_sha256':proof_sha,'checker_stdout':cp.stdout,'checker_stderr':cp.stderr});raise RuntimeError(f'proof check failed at leaf {i}')
  gz=out/'proofs'/f'leaf_{i:04d}.drup.gz'
  with open(proof,'rb') as fi,gzip.open(gz,'wb',compresslevel=6) as fo:
   while True:
    block=fi.read(1<<20)
    if not block:break
    fo.write(block)
  rec={'orbit':i,'status':'VERIFIED_UNSAT','cube':cube,'solver':a.solver,'solve_seconds':solve_seconds,'proof_lines':len(trace),'proof_sha256':proof_sha,'proof_gzip_sha256':sha(gz),'proof_gzip_bytes':gz.stat().st_size,'check_seconds':check_seconds,'checker_stdout':cp.stdout.strip(),'base_sha256':base_sha,'cubes_sha256':cubes_sha}
  atomic_json(out/'results'/f'leaf_{i:04d}.json',rec);records.append(rec);proof.unlink();units.unlink()
  print(json.dumps({'event':'verified','shard':a.shard_index,'position':pos,'count':len(ids),'orbit':i,'solve_seconds':solve_seconds,'check_seconds':check_seconds}),flush=True)
 manifest={'PASS':True,'shard_index':a.shard_index,'shard_count':a.shard_count,'leaf_count':len(ids),'orbit_ids':ids,'base_sha256':base_sha,'cubes_sha256':cubes_sha,'elapsed_seconds':time.time()-started,'verified':len(records)}
 atomic_json(out/f'shard_{a.shard_index:02d}.json',manifest)
if __name__=='__main__':main()
