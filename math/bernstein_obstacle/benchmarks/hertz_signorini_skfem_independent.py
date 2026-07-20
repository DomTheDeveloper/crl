#!/usr/bin/env python3
"""Independent scikit-fem curved P2 Hertz/Signorini replication.

This implementation uses scikit-fem for curved isoparametric P2 elasticity
assembly. It shares only the geometric mesh generator and physical parameters
with the custom Bernstein assembler. Contact is imposed through the exact
quadratic Bernstein coefficients of each curved edge gap, expressed as linear
combinations of P2 Lagrange trace degrees of freedom.
"""
from __future__ import annotations

import argparse, json, math, sys
from pathlib import Path
import numpy as np
import pandas as pd
from scipy.optimize import LinearConstraint, minimize
from scipy.sparse import bmat, csr_matrix
from scipy.sparse.linalg import spsolve
from skfem import MeshTri, MeshTri2, Basis, FacetBasis, ElementTriP2, ElementVector, asm, LinearForm
from skfem.models.elasticity import linear_elasticity

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import hertz_signorini_p2_bernstein as custom


def build_curved_mesh(radius, nr, na):
    data=custom.make_mesh(radius,nr,na)
    m1=MeshTri(data['points'].T, data['triangles'].T, sort_t=False)
    bfac=m1.boundary_facets(); p=m1.p; facets=m1.facets; tol=1e-9
    top=[]; sym=[]; contact=[]
    for f in bfac:
        a,b=facets[:,f]; pa,pb=p[:,a],p[:,b]
        if abs(pa[1]-radius)<tol and abs(pb[1]-radius)<tol: top.append(int(f))
        if abs(pa[0])<tol and abs(pb[0])<tol: sym.append(int(f))
        ra=np.linalg.norm(pa-np.array([0.,radius])); rb=np.linalg.norm(pb-np.array([0.,radius]))
        if abs(ra-radius)<tol and abs(rb-radius)<tol: contact.append(int(f))
    m2=MeshTri2.from_mesh(m1); nv=m1.nvertices; center=np.array([0.,radius])
    for f in contact:
        a,b=facets[:,f]; pa,pb=p[:,a],p[:,b]
        aa=math.atan2(pa[1]-radius,pa[0]); ab=math.atan2(pb[1]-radius,pb[0])
        am=.5*(aa+ab); M=center+radius*np.array([math.cos(am),math.sin(am)])
        m2.doflocs[:,nv+f]=M
    return m2, np.asarray(top,int), np.asarray(sym,int), np.asarray(contact,int)


def assemble_system(radius,young,poisson,pressure,nr,na):
    mesh,top,sym,contact=build_curved_mesh(radius,nr,na)
    elem=ElementVector(ElementTriP2()); basis=Basis(mesh,elem,intorder=6)
    mu=young/(2*(1+poisson)); lam=young*poisson/((1+poisson)*(1-2*poisson))
    K=asm(linear_elasticity(lam,mu),basis).tocsr()
    @LinearForm
    def top_load(v,w): return -pressure*v[1]
    F=asm(top_load,FacetBasis(mesh,elem,facets=top,intorder=6))
    fixed=basis.get_dofs(facets=sym).all(['u^1']); allidx=np.arange(basis.N)
    free=np.setdiff1d(allidx,fixed); inv=-np.ones(basis.N,dtype=int); inv[free]=np.arange(len(free))
    Kr=K[free][:,free].tocsr(); Fr=F[free]; nv=mesh.nvertices
    contact_vertices=np.unique(mesh.facets[:,contact]); rows=[]; rhs=[]; xpos=[]
    for q in contact_vertices:
        rows.append({inv[2*q+1]:1.0}); rhs.append(-mesh.doflocs[1,q]); xpos.append(mesh.doflocs[0,q])
    for f in contact:
        a,b=mesh.facets[:,f]; m=nv+f
        rows.append({inv[2*m+1]:2.0,inv[2*a+1]:-.5,inv[2*b+1]:-.5})
        Y=2*mesh.doflocs[1,m]-.5*mesh.doflocs[1,a]-.5*mesh.doflocs[1,b]
        rhs.append(-Y); xpos.append(mesh.doflocs[0,m])
    C=csr_matrix((len(rows),len(free))).tolil()
    for i,row in enumerate(rows):
        for j,v in row.items(): C[i,j]=v
    return mesh,basis,free,Kr,Fr,C.tocsr(),np.asarray(rhs),np.asarray(xpos),contact


def solve_pdas(K,f,C,d,maxit=100,tol=1e-9):
    m=C.shape[0]; active=np.ones(m,dtype=bool); last=None
    u=np.zeros(K.shape[0]); lam=np.zeros(m)
    for it in range(1,maxit+1):
        A=C[active]
        if A.shape[0]:
            saddle=bmat([[K,-A.T],[A,None]],format='csr')
            sol=spsolve(saddle,np.r_[f,d[active]])
            u=sol[:K.shape[0]]; lam=np.zeros(m); lam[active]=sol[K.shape[0]:]
        else:
            u=spsolve(K,f); lam=np.zeros(m)
        gap=C@u-d; new=(lam-gap)>0; stat=K@u-f-C.T@lam
        res=max(float(np.max(np.maximum(-gap,0))),float(np.max(np.maximum(-lam,0))),
                float(np.max(np.abs(np.minimum(gap,lam)))),float(np.max(np.abs(stat))))
        if last is not None and np.array_equal(new,last) and res<tol: return u,lam,it,res
        last=active.copy(); active=new
    raise RuntimeError('PDAS did not converge')


def reference_halfwidth(R,E,nu,p):
    return 2*math.sqrt(2*R*R*p*(1-nu*nu)/(E*math.pi))


def run_case(nr,na):
    R,E,nu,p=1.,200.,.3,.5
    mesh,basis,free,Kr,Fr,C,d,xpos,contact=assemble_system(R,E,nu,p,nr,na)
    ur,lam,it,res=solve_pdas(Kr,Fr,C,d); gap=C@ur-d; b=reference_halfwidth(R,E,nu,p)
    xx=np.sort(xpos[gap<=1e-9]); xmax=xx[-1]; future=np.sort(xpos[xpos>xmax+1e-12])
    bh=.5*(xmax+future[0]) if len(future) else xmax
    maxrad=0.; t=np.linspace(0,1,401)
    N=np.column_stack((2*(t-.5)*(t-1),4*t*(1-t),2*t*(t-.5)))
    nv=mesh.nvertices; center=np.array([0.,R])
    for fct in contact:
        a,bb=mesh.facets[:,fct]; m=nv+fct; pts=N@mesh.doflocs[:,[a,m,bb]].T
        maxrad=max(maxrad,float(np.max(np.abs(np.linalg.norm(pts-center,axis=1)-R))))
    return {'radial_intervals':nr,'angular_intervals':na,'vertices':mesh.nvertices,
            'displacement_unknowns':len(free),'constraints':C.shape[0],'pdas_iterations':it,
            'kkt_residual':res,'exact_contact_half_width':b,'estimated_contact_half_width':bh,
            'contact_half_width_error':abs(bh-b),'total_half_reaction':float(np.sum(lam)),
            'reaction_error':abs(float(np.sum(lam))-p*R),'minimum_gap_coefficient':float(np.min(gap)),
            'maximum_boundary_radius_error':maxrad}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--comparison',type=Path,required=True); ap.add_argument('--reference',type=Path,required=True)
    args=ap.parse_args(); cases=[(4,40),(6,60),(8,80),(12,120),(16,160)]
    rows=[]
    for c in cases:
        row=run_case(*c); rows.append({k:(v.item() if hasattr(v,'item') else v) for k,v in row.items()})
    frame=pd.DataFrame(rows); frame.to_csv(args.output,index=False)
    reference=pd.read_csv(args.reference)
    merged=frame.merge(reference,on=['radial_intervals','angular_intervals'],suffixes=('_skfem','_custom'))
    comparison=[]
    for _,r in merged.iterrows():
        comparison.append({'radial_intervals':int(r['radial_intervals']),'angular_intervals':int(r['angular_intervals']),
          'halfwidth_absolute_difference':abs(float(r['estimated_contact_half_width'])-float(r['bracketed_contact_half_width'])),
          'reaction_absolute_difference':abs(float(r['total_half_reaction_skfem'])-float(r['total_half_reaction_custom'])),
          'geometry_radius_error_difference':abs(float(r['maximum_boundary_radius_error_skfem'])-float(r['maximum_boundary_radius_error_custom'])),
          'minimum_gap_skfem':float(r['minimum_gap_coefficient_skfem']),'minimum_gap_custom':float(r['minimum_gap_coefficient_custom'])})
    payload={'framework':'scikit-fem 12.0.2','cases':comparison,
      'maximum_halfwidth_difference':max(x['halfwidth_absolute_difference'] for x in comparison),
      'maximum_reaction_difference':max(x['reaction_absolute_difference'] for x in comparison),
      'maximum_geometry_error_difference':max(x['geometry_radius_error_difference'] for x in comparison)}
    args.comparison.write_text(json.dumps(payload,indent=2),encoding='utf-8')
    print(frame.to_string(index=False)); print(json.dumps(payload,indent=2))

if __name__=='__main__': main()
