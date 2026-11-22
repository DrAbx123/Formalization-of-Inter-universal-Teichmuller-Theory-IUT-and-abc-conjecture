# -*- coding: utf-8 -*-
import io, sys
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
def mod(a): return divmod(a,f)[1]
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
        if c%q:
            terms.append(f"monomial {i} ({c%q} : ZMod 29)")
    if not terms: return f"def {name} : (ZMod 29)[X] := 0"
    return "def "+name+" : (ZMod 29)[X] :=\n  " + " +\n  ".join(terms)

xp=[0]*30; xp[29]=1
Q1,P1=divmod(xp,f)
R=[ [1], P1 ]
S=[None,None]
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
# scale to 1
def scale(a,c): return trim([(x*c)%q for x in a])
inv2=pow(gg2[0],q-2,q); inv5=pow(gg5[0],q-2,q)
A2s=scale(A2,inv2); B2s=scale(B2,inv2); A5s=scale(A5,inv5); B5s=scale(B5,inv5)

def def_lines():
    lines=[]
    lines.append(fmt_mono('f',f))
    lines.append(fmt_mono('P1',P1))
    for i in range(2,11): lines.append(fmt_mono(f'P{i}',P[i]))
    lines.append(fmt_mono('R0',[1]))
    for j in range(1,10): lines.append(fmt_mono(f'R{j}',R[j]))
    lines.append(fmt_mono('Q1',Q1))
    for j in range(2,10): lines.append(fmt_mono(f'S{j}',S[j]))
    lines.append(fmt_mono('A2',A2s)); lines.append(fmt_mono('B2',B2s))
    lines.append(fmt_mono('A5',A5s)); lines.append(fmt_mono('B5',B5s))
    return "\n\n".join(lines)

def coeff_tactic(defs, lhs, rhs, N, mul=True, extra=[]):
    s = ["by","  ext k","  by_cases hk : k ≤ "+str(N),"  · interval_cases k <;>"]
    inner = []
    if mul:
        inner.append("rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]")
    names = ", ".join(defs + extra)
    inner.append("simp ["+names+", coeff_monomial, coeff_X_pow, coeff_add, coeff_sub, coeff_C_mul, coeff_sum, Finset.sum_range_succ]")
    inner.append("try reduce_mod_char")
    s.append("      (" + "\n       ".join(inner) + ")")
    s.append("  · have hL : ("+lhs+").coeff k = 0 := by")
    s.append("      apply coeff_eq_zero_of_natDegree_lt (p := "+lhs+")")
    s.append("      have hdeg : ("+lhs+").natDegree < "+str(N+1)+" := by compute_degree!")
    s.append("      omega")
    s.append("    have hR : ("+rhs+").coeff k = 0 := by")
    s.append("      apply coeff_eq_zero_of_natDegree_lt (p := "+rhs+")")
    s.append("      have hdeg : ("+rhs+").natDegree < "+str(N+1)+" := by compute_degree!")
    s.append("      omega")
    s.append("    rw [hL, hR]")
    return "\n".join(s)

def lemma(name, lhs, rhs, N, defs, mul=True, extra=[]):
    return "lemma "+name+" : "+lhs+" = "+rhs+" := "+coeff_tactic(defs,lhs,rhs,N,mul,extra)

lemmas=[]
lemmas.append(lemma('cert_P1', '(X : (ZMod 29)[X])^29 - P1', 'f * Q1', 29, ['f','P1','Q1']))
lemmas.append(lemma('cert_R2', 'R1 * P1 - R2', 'f * S2', 18, ['R1','P1','R2','f','S2']))
# linear P2
# rhs sum
lim = " + ".join([f"C (P1.coeff {j}) * R{j}" for j in range(10)])
lemmas.append(lemma('cert_lin1', 'P2', '('+lim+')', 9, ['P2','P1','R0','R1','R2','R3','R4','R5','R6','R7','R8','R9'], mul=False))
# bezout2
lemmas.append(lemma('cert_bez2', 'A2 * f + B2 * (P2 - X)', '1', 19, ['A2','B2','f','P2']))

header = """import Mathlib

open Polynomial

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

variable (x : (AdjoinRoot f))

"""
content = header + def_lines() + "\n\n" + "\n\n".join(lemmas) + "\n"
open('tmp/sheaf/xif/paper/_S2094gen_test.lean','w',encoding='utf-8').write(content)
print('wrote', len(content), 'chars')
print('Q1',Q1)
print('S2',S[2])
print('B2',B2s, 'A2', A2s)
