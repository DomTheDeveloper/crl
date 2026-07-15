#!/usr/bin/env python3
"""Run Simon two-descent on the three reduced quadratic Prym twists."""
import json,sys,time,traceback
from pathlib import Path
from sage.all import QQ, PolynomialRing, NumberField, EllipticCurve

orb=int(sys.argv[1]) if len(sys.argv)>1 else 0
R=PolynomialRing(QQ,'z'); z=R.gen(); K=NumberField(z*z-128535,'w'); w=K.gen()
A0=K(-13655564670); B0=K(611545278434200)
deltas=[
 K(QQ(14886939375)/3911011)-K(QQ(13140225)/15644044)*w,
 K(QQ(365581755)/105703)-K(QQ(730863)/422812)*w,
 K(QQ(897001875)/300847)-K(QQ(3085425)/1203388)*w,
]
d=deltas[orb]
E=EllipticCurve(K,[0,0,0,A0*d*d,B0*d*d*d])
out={'orbit':orb,'field_polynomial':str(K.polynomial()),'delta':str(d),
     'ainvs':[str(x) for x in E.a_invariants()],'j':str(E.j_invariant()),
     'torsion_order':int(E.torsion_subgroup().order())}
st=time.time()
try:
 ans=E.simon_two_descent(verbose=1,lim1=1,lim3=1,limtriv=1,maxprob=8,limbigprime=20)
 out['lower']=int(ans[0]);out['upper']=int(ans[1])
 out['points']=[[str(c) for c in P] for P in ans[2]]
except Exception as exc:
 out['error']=f'{type(exc).__name__}: {exc}'
 out['traceback']=traceback.format_exc(limit=20)
out['elapsed']=time.time()-st
Path('results').mkdir(exist_ok=True)
Path(f'results/quad_small_{orb}.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps(out,sort_keys=True))
