# -*- coding: utf-8 -*-
q=29
f=[10,24,16,14,24,8,5,7,0,25,1]
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
def fmt_mono(name,a):
    terms=[f"monomial {i} ({c%q} : ZMod 29)" for i,c in enumerate(a) if c%q]
    if not terms: return f"def {name} : (ZMod 29)[X] := 0"
    return "def "+name+" : (ZMod 29)[X] :=\n  "+" +\n  ".join(terms)
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
def_lines=[fmt_mono('P1',P1),fmt_mono('P2',P[2])]
for j in range(10): def_lines.append(fmt_mono(f'R{j}',R[j]))
def_lines.append("""def Rfun : ℕ → (ZMod 29)[X]
  | 0 => R0
  | 1 => R1
  | 2 => R2
  | 3 => R3
  | 4 => R4
  | 5 => R5
  | 6 => R6
  | 7 => R7
  | 8 => R8
  | 9 => R9
  | _ => 0""")
# explicit cert_lin1 from generator template (known to compile)
lim=" + ".join([f"C (P1.coeff {j}) * R{j}" for j in range(10)])
header="import Mathlib\nopen Polynomial\nlocal instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩\nnoncomputable section\nset_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\n\n"
cert = "lemma cert_lin1 : P2 = ("+lim+") := by\n  ext k\n  by_cases hk : k ≤ 9\n  · interval_cases k <;>\n      (try simp only [coeff_add, coeff_sub]\n       try repeat rw [coeff_mul]\n       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]\n       try simp [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]\n       try reduce_mod_char)\n  · have hL : (P2).coeff k = 0 := by\n      apply coeff_eq_zero_of_natDegree_lt (p := P2)\n      have hdeg : (P2).natDegree < 10 := by\n        simp only [P2]\n        compute_degree!\n      omega\n    have hR : ("+lim+").coeff k = 0 := by\n      apply coeff_eq_zero_of_natDegree_lt (p := ("+lim+"))\n      have hdeg : ("+lim+").natDegree < 10 := by\n        simp only [P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]\n        compute_degree!\n      omega\n    rw [hL, hR]\n"
conv = "lemma hlin1' : P2 = ∑ j ∈ Finset.range 10, C (P1.coeff j) * Rfun j := by\n  rw [cert_lin1]\n  simp [Finset.sum_range_succ, Rfun]\n"
content=header+"\n\n".join(def_lines)+"\n\n"+cert+"\n"+conv
open('tmp/sheaf/xif/paper/_S2094gen_convert.lean','w',encoding='utf-8').write(content)
print('wrote',len(content))
