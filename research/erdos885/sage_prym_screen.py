#!/usr/bin/env python3
"""Construct a friendly Case-1 Prym elliptic curve for each of the four
known A-orbits on the best diagonal genus-5 curve.

We use Stoll's Case 1 with ordered indices
  (i,j,k,l,m)=(0,3,1,2,4),
where coordinate 4 is z.  The corresponding biquadratic field is
  K=Q(sqrt(1/4234275), sqrt(1/3735200))
   =Q(sqrt(2091),sqrt(9338)).

After parametrising the conic
  a'' u_l^2 = u_m^2-b''u_j^2
through the selected known point, the Prym genus-one curve becomes a binary
quartic y^2=g(T).  We compute its classical invariants and the Jacobian model
  Y^2=X^3-27 I X-27 J.
The script then tries every Sage/Pari rank interface available over K and
records proof status rather than silently treating a heuristic as certified.
"""
from __future__ import annotations

import json
import traceback
from pathlib import Path

from sage.all import EllipticCurve, Integer, NumberField, PolynomialRing, QQ, proof

ROWS=[Integer(x) for x in [2578,5553,5922,3222]]
# vectors for u_0^2,...,u_3^2,z^2 as linear forms in (x,z^2)
V=[(QQ(1),QQ(r*r)) for r in ROWS]+[(QQ(0),QQ(1))]
PERM=(0,3,1,2,4)  # i,j,k,l,m


def relation(k,l,m):
    xk,yk=V[k];xl,yl=V[l];xm,ym=V[m]
    det=xk*yl-xl*yk
    a=(xm*yl-xl*ym)/det
    b=(xk*ym-xm*yk)/det
    return a,b


def known_orbits():
    out=[]
    for t in [-5585184,0,35994816]:
        coords=[]
        for r in ROWS:
            n=Integer(t)+r*r
            if n<0 or not n.is_square(): raise RuntimeError('bad known column')
            coords.append(QQ(n.sqrt()))
        coords.append(QQ(1))
        out.append((f't={t}',coords))
    out.append(('infinity',[QQ(1),QQ(1),QQ(1),QQ(1),QQ(0)]))
    return out


def quartic_invariants(poly):
    # poly = e + d*T + c*T^2 + b*T^3 + a*T^4
    a=poly[4];b=poly[3];c=poly[2];d=poly[1];e=poly[0]
    I=12*a*e-3*b*d+c*c
    J=72*a*c*e+9*b*c*d-27*a*d*d-27*b*b*e-2*c*c*c
    return I,J


def main():
    i,j,k,l,m=PERM
    a,b=relation(k,l,m)
    ap,bp=relation(i,j,m)
    app,bpp=relation(l,j,m)

    Z=PolynomialRing(QQ,'z').gen()
    minpoly=Z**4-2*(b+bp)*Z**2+(b-bp)**2
    K=NumberField(minpoly,'theta')
    th=K.gen()
    alpha=(th**2+K(b)-K(bp))/(2*th)
    beta=(th**2-K(b)+K(bp))/(2*th)
    if alpha**2 != K(b) or beta**2 != K(bp):
        raise RuntimeError('failed to recover square roots')
    KT=PolynomialRing(K,'T');T=KT.gen()

    report={
      'permutation':list(PERM),
      'relations':{'a':str(a),'b':str(b),'ap':str(ap),'bp':str(bp),'app':str(app),'bpp':str(bpp)},
      'field_minpoly':str(minpoly),'field_degree':int(K.degree()),
      'field_discriminant':str(K.discriminant()),
      'alpha':str(alpha),'beta':str(beta),'orbits':[]}

    for label,v in known_orbits():
        rec={'label':label,'point':[str(x) for x in v]}
        try:
            if v[l]==0: raise RuntimeError('chosen conic chart has v_l=0')
            j0=K(v[j]/v[l]);m0=K(v[m]/v[l])
            D=T*T-K(bpp)
            NJ=j0*(T*T+K(bpp))-2*m0*T
            NM=-m0*(T*T+K(bpp))+2*K(bpp)*j0*T
            gamma=(K(v[m])-alpha*K(v[l]))*(K(v[m])-beta*K(v[j]))
            g=(gamma*(NM-alpha*D)*(NM-beta*NJ)).polynomial(KT)
            if g.degree()!=4: raise RuntimeError(f'quartic degree {g.degree()}')
            I,J=quartic_invariants(g)
            E=EllipticCurve(K,[0,0,0,-27*I,-27*J])
            rec.update({
              'gamma':str(gamma),
              'quartic_coefficients':[str(g[n]) for n in range(5)],
              'I':str(I),'J':str(J),
              'elliptic_ainvs':[str(x) for x in E.a_invariants()],
              'elliptic_discriminant':str(E.discriminant()),
              'j_invariant':str(E.j_invariant()),
              'j_is_rational':bool(E.j_invariant() in QQ),
              'torsion_order':int(E.torsion_subgroup().order()),
            })
            # Record available interfaces separately.
            try:
                proof.all(False)
                gs=E.gens(proof=False)
                rec['gens_heuristic']=[[str(P[0]),str(P[1]),str(P[2])] for P in gs]
                rec['rank_lower_from_gens']=len(gs)
                rec['gens_certain']=bool(E.gens_certain()) if hasattr(E,'gens_certain') else None
            except Exception as exc:
                rec['gens_error']=f'{type(exc).__name__}: {exc}'
                rec['gens_traceback']=traceback.format_exc(limit=8)
            finally:
                proof.all(True)
            try:
                rec['rank_default']=int(E.rank())
            except Exception as exc:
                rec['rank_error']=f'{type(exc).__name__}: {exc}'
            try:
                rec['rank_bounds']=list(map(int,E.rank_bounds()))
            except Exception as exc:
                rec['rank_bounds_error']=f'{type(exc).__name__}: {exc}'
            try:
                rec['two_descent_simon']=str(E.gens(proof=False,algorithm='pari'))
            except Exception as exc:
                rec['pari_gens_error']=f'{type(exc).__name__}: {exc}'
        except Exception as exc:
            rec['construction_error']=f'{type(exc).__name__}: {exc}'
            rec['construction_traceback']=traceback.format_exc(limit=12)
        report['orbits'].append(rec)

    Path('results').mkdir(exist_ok=True)
    Path('results/prym_screen.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,sort_keys=True))

if __name__=='__main__':main()
