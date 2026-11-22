#!/usr/bin/env python3
"""A1081: symbolic cancellation model (SymPy).
Register: capsule i, place v, label/tuple c, label-pow j.
Terms: packetWeight, tame (1-1/e)logp, qScale -j^2 v/(2l), ind2 frac, arch, shellDefect, A, V, gap.
Uses sum_j j^2 = nC*sF, sum weights=1, capsule average 1/nC.
Outputs residual expression and sign tests. Pure SymPy/Python; no Lean/Sage."""
import sympy as sp, random, json, math

l,nC,e,logp,m,F,arch,shell = sp.symbols('l nC e logp m F arch shell', positive=True)
w = sp.symbols('w', real=True)  # packet weight placeholder (sum = 1)
sF = (nC+1)*(2*nC+1)/6
sumj2 = nC*sF
A = m*logp/(2*l)
# hull packet per capsule: sum_c w_c * sum_j (1-1/e)*logp; sum_c w_c=1
hull = nC*(1-1/e)*logp
V = hull  # (1/nC) sum_i hull = hull
# gap packet: sum_c w_c * sum_j frac(j^2 m/(2l))*logp = F*logp, 0<=F<=nC
gap = F*logp
# qScale and ind2 leading: exact per-j cancellation
qscale = -sumj2*m*logp/(2*l)
ind2lead = sumj2*m*logp/(2*l)
cancel = sp.simplify(qscale+ind2lead)
R = sp.simplify(V+gap-(sF-1)*A+arch+shell)
Rfact = sp.factor(R)
print("sF =",sF)
print("sumj2 =",sumj2)
print("qscale+ind2lead =",cancel)
print("R =",R)
print("R factored =",Rfact)
# positivity threshold with F<=nC
maxF = nC
mcrit = sp.simplify(2*l/(sF-1)*(nC*(1-1/e)+maxF+(arch+shell)/logp))
print("mcrit (sufficient positivity up to arch/shell) =",mcrit)
# test l=5 nC=2 e=10 logp=log7
vals={l:5,nC:2,e:10,logp:math.log(7),arch:0.28527176196673965,shell:0,m:1,F:0}
Rl=float(sp.N(R.subs(vals)))
mcrit_l=float(sp.N(mcrit.subs(vals)))
print("l=5,nC=2,e=10,logp=log7: mcrit =",mcrit_l)
# random/grid m up to 1e6, F in [0,nC]
random.seed(1); tests=[]
for mt in [1,5,10,20,24,25,26,30,50,100,1000,10**4,10**5,10**6]:
    for Fi in [0,1,2]:
        val=float(sp.N(R.subs({**vals,m:mt,F:Fi})))
        tests.append(dict(m=mt,F=Fi,R=val,positive=val>0))
neg=sum(1 for t in tests if not t["positive"]); pos=len(tests)-neg
print("grid tests",len(tests),"negative",neg,"positive",pos)
print("examples",tests[:8])
print("large negative examples",[t for t in tests if t["m"]>=10**4][:6])
json.dump(dict(sF=str(sF),sumj2=str(sumj2),cancel=str(cancel),residual=str(R),residual_factored=str(Rfact),
               mcrit=str(mcrit),mcrit_l5=mcrit_l,tests=tests),open("coord/symbolic_cancellation_results.json","w"),indent=1)
