#!/usr/bin/env python3
"""Basis-stable mod-2 -> mod-4 -> mod-8 descent in one Sage process."""
from __future__ import annotations
import json,time
from pathlib import Path
from sage.all import proof
from sage_unified_descent import (certified_factor_data,factor_classes,filter_level,
    lift_candidates,known_projective_points,exact_known_matches,point_json)
import sage_kummer_compat as kc
import sage_kummer_five as k5

def main():
    started=time.time();proof.all(True);factors=certified_factor_data()
    classes2=[factor_classes(FD,2)[0] for FD in factors]
    surv2,sizes2,prog2,used2=filter_level(2,factors,classes2)
    classes4=[];maps4=[]
    for FD in factors:
        reps,mp=factor_classes(FD,4);classes4.append(reps);maps4.append(mp)
    sizes4=[len(x) for x in classes4]
    init4=lift_candidates(surv2,sizes2,classes2,maps4,sizes4)
    surv4,_,prog4,used4=filter_level(4,factors,classes4,init4)
    classes8=[];maps8=[]
    for FD in factors:
        reps,mp=factor_classes(FD,8);classes8.append(reps);maps8.append(mp)
    sizes8=[len(x) for x in classes8]
    init8=lift_candidates(surv4,sizes4,classes4,maps8,sizes8)
    surv8,_,prog8,used8=filter_level(8,factors,classes8,init8)
    known=known_projective_points(factors)
    exact4,err4=exact_known_matches(4,surv4,sizes4,classes4,known)
    exact8,err8=exact_known_matches(8,surv8,sizes8,classes8,known)
    out={
      'rows':[int(x) for x in kc.ROWS],
      'known_columns':list(k5.KNOWN_T),
      'known_projective_point_count':len(known),
      'basis_stability':'All three levels use the same certified generator objects in one Sage process.',
      'factors':[{'kind':FD['kind'],'indices':list(FD.get('inds',())),'rank':FD['rank'],
                  'generators':[point_json(P) for P in FD['gens']]} for FD in factors],
      'mod2':{'survivor_count':len(surv2),'progress':prog2,'used_primes':used2},
      'mod4':{'initial_lifts':len(init4),'survivor_count':len(surv4),'progress':prog4,'used_primes':used4,
              'exact_known_matches':exact4,'division_errors':err4},
      'mod8':{'initial_lifts':len(init8),'survivor_count':len(surv8),'progress':prog8,'used_primes':used8,
              'exact_known_matches':exact8,'division_errors':err8},
      'elapsed_seconds':round(time.time()-started,3),
      'soundness':'Every deletion uses the complete projective curve image in all five quotient groups. No class index crosses a basis computation.'}
    Path('results').mkdir(exist_ok=True)
    Path('results/unified_mod8.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'mod2':len(surv2),'mod4':len(surv4),'mod8':len(surv8),'err4':err4,'err8':err8,'elapsed':out['elapsed_seconds']},sort_keys=True))
if __name__=='__main__':main()
