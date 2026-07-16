#!/usr/bin/env python3
"""Generate exact Lean checks for all outer-certificate interval densities.

Input: the exact q_weights CSV emitted by generate_outer_certificate.py.
Output: a generated Lean module.  The Python quotient-ring arithmetic is not
trusted: every multiplication and every aggregate density identity is replayed
as rational coefficient arithmetic by Lean's kernel.
"""
from __future__ import annotations

import csv
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterDensityCertificate.lean"
P_LO = Fraction(2115883, 10_000_000)
P_HI = Fraction(2115884, 10_000_000)

class K:
    __slots__ = ("a", "b", "c")
    def __init__(self, a=0, b=0, c=0):
        self.a, self.b, self.c = Fraction(a), Fraction(b), Fraction(c)
    def __add__(self, other):
        other = C(other); return K(self.a+other.a, self.b+other.b, self.c+other.c)
    __radd__ = __add__
    def __neg__(self): return K(-self.a, -self.b, -self.c)
    def __sub__(self, other): return self + (-C(other))
    def __rsub__(self, other): return C(other) - self
    def __mul__(self, other):
        other = C(other)
        raw = [Fraction(0) for _ in range(5)]
        for i, x in enumerate((self.a,self.b,self.c)):
            for j, y in enumerate((other.a,other.b,other.c)):
                raw[i+j] += x*y
        return K(raw[0] - Fraction(7,401)*raw[3] - Fraction(2317,160801)*raw[4],
                 raw[1] - Fraction(19,401)*raw[3] - Fraction(9096,160801)*raw[4],
                 raw[2] + Fraction(331,401)*raw[3] + Fraction(101942,160801)*raw[4])
    __rmul__ = __mul__
    def inv(self):
        # Exact 3x3 Gaussian elimination over Q for multiplication by self.
        cols = [self*K(1), self*K(0,1), self*K(0,0,1)]
        aug = [[cols[j].a, cols[j].b, cols[j].c] for j in range(3)]
        A = [[aug[j][i] for j in range(3)] + [Fraction(i == 0)] for i in range(3)]
        for col in range(3):
            pivot = next(r for r in range(col,3) if A[r][col])
            A[col], A[pivot] = A[pivot], A[col]
            scale = A[col][col]
            A[col] = [x/scale for x in A[col]]
            for r in range(3):
                if r == col: continue
                factor = A[r][col]
                if factor:
                    A[r] = [x-factor*y for x,y in zip(A[r],A[col])]
        return K(A[0][3], A[1][3], A[2][3])
    def __truediv__(self, other): return self * C(other).inv()
    def __eq__(self, other):
        other=C(other); return (self.a,self.b,self.c)==(other.a,other.b,other.c)
    def decimal(self, p=0.2115883015630957747):
        return float(self.a)+float(self.b)*p+float(self.c)*p*p

def C(x): return x if isinstance(x,K) else K(x)

def qlean(q: Fraction) -> str:
    q=Fraction(q)
    if q.denominator == 1: return str(q.numerator)
    if q.numerator < 0: return f"(-{abs(q.numerator)} / {q.denominator} : ℚ)"
    return f"({q.numerator} / {q.denominator} : ℚ)"

def rep_literal(x: K) -> str:
    return f"⟨{qlean(x.a)}, {qlean(x.b)}, {qlean(x.c)}⟩"

def sign_kind(x: K) -> str:
    if x.c < 0: return "concave"
    if x.c == 0: return "left" if x.b >= 0 else "right"
    vertex = -x.b/(2*x.c)
    if vertex <= P_LO: return "left"
    if vertex >= P_HI: return "right"
    raise RuntimeError(f"interior minimum for {x.a,x.b,x.c}")

def ordered(mid: K, signed_length: K):
    if signed_length.decimal() >= 0:
        return mid-signed_length*Fraction(1,2), mid+signed_length*Fraction(1,2), signed_length
    return mid+signed_length*Fraction(1,2), mid-signed_length*Fraction(1,2), -signed_length

def emit_pos(out, theorem: str, defname: str, x: K):
    out += [f"theorem {theorem} : 0 < {defname}.eval := by",
            f"  have h : 0 < evalAtCheckerboardP {qlean(x.a)} {qlean(x.b)} {qlean(x.c)} := by"]
    kind=sign_kind(x)
    if kind=="concave":
        out += ["    apply evalAtCheckerboardP_pos_of_concave",
                "    · norm_num",
                "    · norm_num [quadraticAt, pLower]",
                "    · norm_num [quadraticAt, pUpper]"]
    elif kind=="left":
        out += ["    apply evalAtCheckerboardP_pos_of_left",
                "    · norm_num",
                "    · norm_num [pLower]",
                "    · norm_num [quadraticAt, pLower]"]
    else:
        out += ["    apply evalAtCheckerboardP_pos_of_right",
                "    · norm_num",
                "    · norm_num [pUpper]",
                "    · norm_num [quadraticAt, pUpper]"]
    out += [f"  simpa [{defname}, CubicRep.eval, evalAtCheckerboardP, quadraticAt] using h",""]

def emit_eval_sum(out, theorem: str, names: list[str], target: int):
    if not names:
        out += [f"theorem {theorem} : (0 : ℝ) = {target} := by norm_num",""]
        return
    expr=" +\n      ".join(f"{n}.eval" for n in names)
    cexpr=" + ".join(f"(({n}.constant : ℝ))" for n in names)
    lexpr=" + ".join(f"(({n}.linear : ℝ))" for n in names)
    qexpr=" + ".join(f"(({n}.quadratic : ℝ))" for n in names)
    defs=", ".join(names)
    out += [f"theorem {theorem} :",f"    {expr} = {target} := by",
            f"  have hc : {cexpr} = {target} := by norm_num [{defs}]",
            f"  have hl : {lexpr} = 0 := by norm_num [{defs}]",
            f"  have hq : {qexpr} = 0 := by norm_num [{defs}]",
            "  simp only [CubicRep.eval]",
            "  linear_combination hc + checkerboardP * hl + checkerboardP ^ 2 * hq",""]

def generate(rows):
    r=K(Fraction(539,912),Fraction(487,456),Fraction(-1203,304))
    q=K(Fraction(-713,912),Fraction(871,152),Fraction(-6817,912))
    h=K(Fraction(-47,304),Fraction(4739,456),Fraction(-10025,912))
    E=[K(0),q,K(1)-r,h-K(1),r,(h-q)*Fraction(1,2),(h+q)*Fraction(1,2),K(1)]
    comps=[]
    for row in rows:
        w=K(Fraction(row['weight_const']),Fraction(row['weight_p']),Fraction(row['weight_p2']))
        ai,aj=int(row['A_lo_idx']),int(row['A_hi_idx'])
        bi,bj=int(row['B_lo_idx']),int(row['B_hi_idx'])
        sigma=int(row['sigma'])
        la,lb=E[aj]-E[ai],E[bj]-E[bi]
        ma,mb=(E[ai]+E[aj])*Fraction(1,2),(E[bi]+E[bj])*Fraction(1,2)
        slo,shi,slen=ordered(ma+mb,la+sigma*lb)
        dlo,dhi,dlen=ordered(ma-mb,la-sigma*lb)
        comp=dict(w=w,ai=ai,aj=aj,bi=bi,bj=bj,sigma=sigma,
            la=la,lb=lb,slo=slo,shi=shi,slen=slen,dlo=dlo,dhi=dhi,dlen=dlen,
            aden=w/la,bden=w/lb,sden=w/slen,dden=w/dlen)
        assert comp['aden']*la == w and comp['bden']*lb == w
        assert comp['sden']*slen == w and comp['dden']*dlen == w
        comps.append(comp)

    out=["import Checkerboard.LP.CubicField",
         "import Checkerboard.LP.CubicInterval",
         "import Checkerboard.LP.PrimalParameterBounds",
         "import Checkerboard.LP.OuterCertificateData","",
         "/-!","# Generated exact outer interval-density certificate","",
         "Generated by `scripts/checkerboard/generate_outer_density_certificate.py`.",
         "All quotient products and aggregate identities are replayed by Lean.","-/","",
         "namespace Checkerboard","","noncomputable section",""]

    for i,x in enumerate(E): out += [f"def outerEndpointRep{i} : CubicRep := {rep_literal(x)}",""]
    for i,z in enumerate(comps):
        out += [f"def outerWeightRep{i} : CubicRep := {rep_literal(z['w'])}",
                f"theorem outerWeightRep{i}_eval : outerWeightRep{i}.eval = outerWeight{i}.eval := by",
                f"  norm_num [outerWeightRep{i}, outerWeight{i}, CubicRep.eval, CubicWeight.eval,",
                "    evalAtCheckerboardP, quadraticAt]",""]
        for key,stem in [('la','ALength'),('lb','BLength'),('slen','SumLength'),('dlen','DiffLength'),
                         ('aden','ADensity'),('bden','BDensity'),('sden','SumDensity'),('dden','DiffDensity'),
                         ('slo','SumLo'),('shi','SumHi'),('dlo','DiffLo'),('dhi','DiffHi')]:
            out += [f"def outer{stem}{i} : CubicRep := {rep_literal(z[key])}",""]
        for stem,key in [('ALength','la'),('BLength','lb'),('SumLength','slen'),('DiffLength','dlen')]:
            emit_pos(out,f"outer{stem}{i}_pos",f"outer{stem}{i}",z[key])
        for denstem,lenstem in [('ADensity','ALength'),('BDensity','BLength'),
                                ('SumDensity','SumLength'),('DiffDensity','DiffLength')]:
            out += [f"theorem outer{denstem}{i}_mul_length :",
                    f"    CubicRep.mul outer{denstem}{i} outer{lenstem}{i} = outerWeightRep{i} := by",
                    "  apply CubicRep.ext <;>",
                    f"    norm_num [outer{denstem}{i}, outer{lenstem}{i}, outerWeightRep{i}, CubicRep.mul]",""]
            out += [f"theorem outer{denstem}{i}_ratio :",
                    f"    outerWeight{i}.eval / outer{lenstem}{i}.eval = outer{denstem}{i}.eval := by",
                    f"  apply (div_eq_iff (ne_of_gt outer{lenstem}{i}_pos)).2",
                    f"  rw [← outerWeightRep{i}_eval]",
                    f"  have h := congrArg CubicRep.eval outer{denstem}{i}_mul_length",
                    "  simpa using h.symm",""]

    for which,cap in [('A','a'),('B','b')]:
        for k in range(7):
            active=[i for i,z in enumerate(comps) if z[cap+'i'] <= k < z[cap+'j']]
            names=[f"outer{which}Density{i}" for i in active]
            emit_eval_sum(out,f"outer{which.lower()}_density_cell{k}_rep",names,1)
            ratio_names=[f"outer{which}Density{i}_ratio" for i in active]
            ratio_expr=" +\n      ".join(f"outerWeight{i}.eval / outer{which}Length{i}.eval" for i in active)
            out += [f"theorem outer_{which.lower()}_marginal_cell{k} :",f"    {ratio_expr} = 1 := by",
                    "  rw ["+", ".join(ratio_names)+"]",
                    f"  exact outer{which.lower()}_density_cell{k}_rep",""]

    breaks=[-r,-q,q,h]
    for z in comps: breaks += [z['slo'],z['shi'],z['dlo'],z['dhi']]
    uniq=[]
    for x in sorted(breaks,key=lambda u:u.decimal()):
        if not uniq or x!=uniq[-1]: uniq.append(x)
    assert len(uniq)==27
    for j,(lo,hi) in enumerate(zip(uniq,uniq[1:])):
        midpoint=(lo.decimal()+hi.decimal())/2
        activeS=[i for i,z in enumerate(comps) if z['slo'].decimal()<midpoint<z['shi'].decimal()]
        activeD=[i for i,z in enumerate(comps) if z['dlo'].decimal()<midpoint<z['dhi'].decimal()]
        target=int((-r.decimal()<midpoint<-q.decimal()) or (q.decimal()<midpoint<h.decimal()))
        names=[f"outerSumDensity{i}" for i in activeS]+[f"outerDiffDensity{i}" for i in activeD]
        total=K()
        for i in activeS: total+=comps[i]['sden']
        for i in activeD: total+=comps[i]['dden']
        assert total==K(target)
        emit_eval_sum(out,f"outer_projection_density_cell{j}_rep",names,target)
        ratios=[f"outerSumDensity{i}_ratio" for i in activeS]+[f"outerDiffDensity{i}_ratio" for i in activeD]
        terms=[f"outerWeight{i}.eval / outerSumLength{i}.eval" for i in activeS]+[
               f"outerWeight{i}.eval / outerDiffLength{i}.eval" for i in activeD]
        expr=" +\n      ".join(terms) if terms else "(0 : ℝ)"
        out += [f"theorem outer_projection_density_cell{j} :",f"    {expr} = {target} := by"]
        if ratios:
            out += ["  rw ["+", ".join(ratios)+"]",f"  exact outer_projection_density_cell{j}_rep",""]
        else:
            out += ["  norm_num",""]

    out += ["end","","end Checkerboard",""]
    return "\n".join(out)


def main():
    rows=list(csv.DictReader(CSV_PATH.open(newline='',encoding='utf-8')))
    if len(rows)!=35: raise SystemExit(f"expected 35 rows, got {len(rows)}")
    LEAN_PATH.parent.mkdir(parents=True,exist_ok=True)
    LEAN_PATH.write_text(generate(rows),encoding='utf-8')
    print(f"wrote {LEAN_PATH}")

if __name__=='__main__': main()
