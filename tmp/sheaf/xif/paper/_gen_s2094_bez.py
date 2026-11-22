# -*- coding: utf-8 -*-
q = 29
f = [10,24,16,14,24,8,5,7,0,25,1]
def trim(a):
    while len(a)>1 and a[-1]%q==0: a.pop()
    return [x%q for x in a]
def add(a,b):
    n=max(len(a),len(b)); return [((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%q for i in range(n)]
def sub(a,b):
    n=max(len(a),len(b)); return [((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%q for i in range(n)]
def mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%q
    return trim(r)
def divmod(a,b):
    a=trim(a[:]); b=trim(b[:]); quot=[0]*(max(0,len(a)-len(b)+1))
    while len(a)>=len(b) and a!=[0]:
        c=a[-1]*pow(b[-1],q-2,q)%q; d=len(a)-len(b); quot[d]=c
        for j in range(len(b)): a[d+j]=(a[d+j]-c*b[j])%q
        a=trim(a)
    return trim(quot),trim(a)
def xgcd(a,b):
    old_r,r=a[:],b[:]; old_s,s=[1],[0]; old_t,t=[0],[1]
    while r!=[0]:
        quot,rem=divmod(old_r,r)
        old_r,r=r,rem
        old_s,s=s,sub(old_s,mul(quot,s))
        old_t,t=t,sub(old_t,mul(quot,t))
    return trim(old_r),trim(old_s),trim(old_t)
def fmt_mono(name, a):
    terms=[]
    for i,c in enumerate(a):
        if c%q: terms.append(f"monomial {i} ({c%q} : ZMod 29)")
    if not terms: return f"def {name} : (ZMod 29)[X] := 0"
    return "def "+name+" : (ZMod 29)[X] :=\n  " + " +\n  ".join(terms)
xp=[0]*30; xp[29]=1
Q1,P1=divmod(xp,f)
R=[[1],P1]; S=[None,None]
for j in range(2,10):
    prod=mul(R[-1],P1); Sj,Rj=divmod(prod,f); S.append(Sj); R.append(Rj)
P=[None,P1]
for i in range(1,10):
    cur=P[i]; new=[0]*10
    for j in range(10):
        b=cur[j] if j<len(cur) else 0
        if b: new=add(new,[(b*x)%q for x in R[j]])
    P.append(trim(new))
g2=sub(P[2],[0,1]); g5=sub(P[5],[0,1])
gg2,A2,B2=xgcd(f,g2); gg5,A5,B5=xgcd(f,g5)
def scale(a,c): return trim([(x*c)%q for x in a])
A2s=scale(A2,pow(gg2[0],q-2,q)); B2s=scale(B2,pow(gg2[0],q-2,q))
A5s=scale(A5,pow(gg5[0],q-2,q)); B5s=scale(B5,pow(gg5[0],q-2,q))
def def_lines():
    return "\n\n".join([fmt_mono('f',f),fmt_mono('P2',P[2]),fmt_mono('P5',P[5]),fmt_mono('G2',g2),fmt_mono('G5',g5),fmt_mono('A2',A2s),fmt_mono('B2',B2s),fmt_mono('A5',A5s),fmt_mono('B5',B5s)])
def neg_branch(lhs,rhs,N,defs,rhs_const):
    ds=", ".join(defs); lines=[]
    for side in ['hL','hR']:
        expr = lhs if side=='hL' else rhs
        lines.append("  have "+side+" : ("+expr+").coeff k = 0 := by")
        lines.append("    apply coeff_eq_zero_of_natDegree_lt (p := "+expr+")")
        lines.append("    have hdeg : ("+expr+").natDegree < "+str(N+1)+" := by")
        if side=='hR' and rhs_const:
            lines.append("      norm_num")
        else:
            lines.append("      simp only ["+ds+"]")
            lines.append("      compute_degree!")
        lines.append("    omega")
    lines.append("  rw [hL, hR]")
    return "\n".join(lines)
def coeff_tactic(defs,lhs,rhs,N,rhs_const=False):
    simpnames=", ".join(defs+["coeff_monomial","coeff_X_pow","coeff_X","coeff_C","coeff_C_mul","coeff_sum","coeff_one","Finset.sum_range_succ"])
    inner=["try simp only [coeff_add, coeff_sub]",
           "try repeat rw [coeff_mul]",
           "try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]",
           "try simp ["+simpnames+"]",
           "try reduce_mod_char"]
    s=["by","  ext k","  by_cases hk : k ≤ "+str(N),"  · interval_cases k <;>"]
    s.append("      ("+"\n       ".join(inner)+")")
    s.append(neg_branch(lhs,rhs,N,defs,rhs_const))
    return "\n".join(s)
def lemma(name,lhs,rhs,N,defs,rhs_const=False):
    return "lemma "+name+" : "+lhs+" = "+rhs+" := "+coeff_tactic(defs,lhs,rhs,N,rhs_const)
lemmas=[lemma('cert_bez2','A2 * f + B2 * G2','(1 : (ZMod 29)[X])',19,['A2','B2','f','G2'],True),
        lemma('cert_bez5','A5 * f + B5 * G5','(1 : (ZMod 29)[X])',19,['A5','B5','f','G5'],True)]
header="""import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

"""
content=header+def_lines()+"\n\n"+"\n\n".join(lemmas)+"\n"
open('tmp/sheaf/xif/paper/_S2094gen_bez.lean','w',encoding='utf-8').write(content)
print('wrote',len(content))
