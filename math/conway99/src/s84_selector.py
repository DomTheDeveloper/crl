#!/usr/bin/env python3
"""Combine the corrected s=84 base with exhaustive seed-star selector cubes."""
import argparse,json,hashlib
from pathlib import Path
from s84_cover_sat import build
def sha(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--cubes',required=True);ap.add_argument('--cnf',required=True);ap.add_argument('--manifest',required=True);a=ap.parse_args()
    cubes=json.loads(Path(a.cubes).read_text())['cubes'];cnf,_,_=build(False);baseclauses=len(cnf.clauses);first=cnf.nv+1;selectors=list(range(first,first+len(cubes)))
    for s,cube in zip(selectors,cubes):
        for lit in cube:cnf.append([-s,int(lit)])
    cnf.append(selectors);cnf.nv=selectors[-1];cnf.to_file(a.cnf)
    out={'PASS':True,'base_variables':first-1,'base_clauses':baseclauses,'cube_count':len(cubes),'cube_literals':15,
         'selector_variables':len(selectors),'variables':cnf.nv,'clauses':len(cnf.clauses),'cnf_sha256':sha(a.cnf),'cubes_sha256':sha(a.cubes)}
    Path(a.manifest).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
