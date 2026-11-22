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

def defs():
    lines=[fmt_mono('f',f),fmt_mono('P1',P1)]
    for i in range(2,11): lines.append(fmt_mono(f'P{i}',P[i]))
    lines.append(fmt_mono('R0',[1]))
    for j in range(1,10): lines.append(fmt_mono(f'R{j}',R[j]))
    lines.append(fmt_mono('Q1',Q1))
    for j in range(2,10): lines.append(fmt_mono(f'S{j}',S[j]))
    lines.append("""def Rfun : ℕ → (ZMod 29)[X]
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
    return "\n\n".join(lines)

# general lemmas copied from probe77
general = r'''
lemma X_pow_card_sub_X_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] :
    ((X : K[X]) ^ Nat.card K - X) ∣ ((X : K[X]) ^ (Nat.card K)^2 - X) := by
  have hqpos : 0 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hq : 1 ≤ Nat.card K := hqpos
  have hdiv : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
    have h := Nat.pow_sub_one_dvd_pow_sub_one (x := Nat.card K) (m := 1) (k := 2) (by norm_num)
    simpa using h
  obtain ⟨c, hc⟩ := hdiv
  have hpoly : (X : K[X]) ^ (Nat.card K - 1) - 1 ∣ (X : K[X]) ^ (Nat.card K ^ 2 - 1) - 1 := by
    rw [hc]
    exact pow_one_sub_dvd_pow_mul_sub_one X (Nat.card K - 1) c
  have hmul := mul_dvd_mul_left (X : K[X]) hpoly
  convert hmul using 1
  · rw [mul_sub, mul_one, ← pow_succ']
    rw [Nat.sub_add_cancel hq]
  · rw [mul_sub, mul_one, ← pow_succ']
    rw [Nat.sub_add_cancel (Nat.one_le_pow 2 (Nat.card K) hqpos)]

lemma irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] {g : K[X]} (hg : Irreducible g) :
    g ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra K (AdjoinRoot g) := inferInstance
  let pb : PowerBasis K (AdjoinRoot g) := AdjoinRoot.powerBasis hg.ne_zero
  haveI : Module.Finite K (AdjoinRoot g) := pb.finite
  haveI : Fintype (AdjoinRoot g) := Fintype.ofEquiv (Fin pb.dim → K) pb.basis.equivFun.symm.toEquiv
  have hfr : Module.finrank K (AdjoinRoot g) = g.natDegree := by
    rw [pb.finrank]
    rfl
  have hcard : Nat.card (AdjoinRoot g) = Nat.card K ^ g.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K), hfr]
  have hroot : aeval (AdjoinRoot.root g) ((X : K[X]) ^ (Nat.card K) ^ g.natDegree - X) = 0 := by
    simp only [map_sub, map_pow, aeval_X]
    have hpow : (AdjoinRoot.root g) ^ (Nat.card K ^ g.natDegree) = AdjoinRoot.root g := by
      rw [← hcard]
      simpa [Nat.card_eq_fintype_card] using (FiniteField.pow_card (AdjoinRoot.root g))
    rw [hpow, sub_self]
  have hdvd : minpoly K (AdjoinRoot.root g) ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X :=
    minpoly.dvd K _ hroot
  have hmin : minpoly K (AdjoinRoot.root g) = g * C g.leadingCoeff⁻¹ :=
    AdjoinRoot.minpoly_root hg.ne_zero
  have hgdvd : g ∣ minpoly K (AdjoinRoot.root g) := by
    rw [hmin]
    exact dvd_mul_right _ _
  exact hgdvd.trans hdvd

theorem irreducible_of_degree_ten
    {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hm : f.Monic) (hdeg : f.natDegree = 10)
    (hdvd : f ∣ (X : K[X]) ^ (Nat.card K) ^ 10 - X)
    (h2 : IsCoprime f ((X : K[X]) ^ (Nat.card K) ^ 2 - X))
    (h5 : IsCoprime f ((X : K[X]) ^ (Nat.card K) ^ 5 - X)) :
    Irreducible f := by
  by_contra hf
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfunit : ¬ IsUnit f := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfunit hf0
  have hg_dvd_E : g ∣ (X : K[X]) ^ (Nat.card K) ^ 10 - X := hg_dvd.trans hdvd
  have hdvd10 : g.natDegree ∣ 10 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr hg_dvd_E
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 10 := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hg_dvd hf0
  have hgne : g.natDegree ≠ 10 := by
    intro h10
    have hassoc : Associated g f := associated_of_dvd_of_natDegree_le hg_dvd hf0 (by omega)
    exact hf (hassoc.irreducible hg_irr)
  set d := g.natDegree with hddef
  have hdvd10' : d ∣ 10 := by simpa [hddef] using hdvd10
  have hlt' : d < 10 := by simpa [hddef] using lt_of_le_of_ne hgle hgne
  have hpos' : 0 < d := by simpa [hddef] using hgpos
  have hcases : d = 1 ∨ d = 2 ∨ d = 5 := by
    interval_cases d <;> norm_num at hdvd10' <;> norm_num
  rcases hcases with h1 | h2d | h5d
  · have hgd : g.natDegree = 1 := by omega
    have hg1 : g ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X :=
      irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg1' : g ∣ (X : K[X]) ^ Nat.card K - X := by simpa [hgd] using hg1
    have hg2 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 2 - X :=
      hg1'.trans (X_pow_card_sub_X_dvd_X_pow_card_pow_sub_X (K := K))
    exact hg_irr.not_isUnit (h2.isUnit_of_dvd' hg_dvd hg2)
  · have hgd : g.natDegree = 2 := by omega
    have hg2 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 2 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h2.isUnit_of_dvd' hg_dvd hg2)
  · have hgd : g.natDegree = 5 := by omega
    have hg5 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 5 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h5.isUnit_of_dvd' hg_dvd hg5)
'''

# degree lemmas
deg_lines=["lemma hfdeg : f.natDegree = 10 := by\n  unfold f\n  compute_degree!"]
deg_lines.append("lemma hfmonic : f.Monic := by\n  rw [Monic, hfdeg]\n  unfold f\n  norm_num")
for i in range(1,11):
    deg_lines.append(f"lemma hP{i}deg : P{i}.natDegree < 10 := by\n  unfold P{i}\n  compute_degree!")

# hlin' conversions
conv_lines=[]
for i in range(1,10):
    conv_lines.append(f"lemma hlin{i}' : P{i+1} = ∑ j ∈ Finset.range 10, C (P{i}.coeff j) * Rfun j := by\n  rw [cert_lin{i}]\n  simp [Finset.sum_range_succ, Rfun]")

# main theorem
main=[]
main.append("theorem s2094_f_irreducible : Irreducible f := by")
main.append("  let x : AdjoinRoot f := AdjoinRoot.root f")
main.append("""  haveI : CharP (AdjoinRoot f) 29 := by
    have hdeg0 : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hfmonic.ne_zero, hfdeg]
      norm_num
    have hinj : Function.Injective (algebraMap (ZMod 29) (AdjoinRoot f)) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg0
    exact charP_of_injective_algebraMap hinj 29""")
main.append("""  have hpow1 : x ^ 29 = aeval x P1 := by
    have h : aeval x ((X : (ZMod 29)[X]) ^ 29 - P1) = 0 := by
      rw [cert_P1]
      simp [AdjoinRoot.aeval_eq]
    have h' : x ^ 29 - aeval x P1 = 0 := by simpa using h
    exact sub_eq_zero.mp h'""")
main.append("  have hR0 : (aeval x P1)^0 = aeval x (Rfun 0) := by simp [Rfun, R0]")
main.append("  have hR1 : (aeval x P1)^1 = aeval x (Rfun 1) := by simp [Rfun, R1, P1]")
for j in range(2,10):
    main.append(f"""  have hR{j} : (aeval x P1)^{j} = aeval x (Rfun {j}) := by
    have h : aeval x (R{j-1} * P1 - R{j}) = 0 := by
      rw [cert_R{j}]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R{j-1} * P1) = aeval x R{j} := sub_eq_zero.mp h
    calc
      (aeval x P1)^{j} = (aeval x P1)^{j-1} * aeval x P1 := by
        rw [show {j} = {j-1} + 1 by norm_num, pow_succ]
      _ = aeval x R{j-1} * aeval x P1 := by rw [hR{j-1}]
      _ = aeval x (R{j-1} * P1) := by rw [map_mul]
      _ = aeval x R{j} := h'
      _ = aeval x (Rfun {j}) := by simp [Rfun, R{j}]""")
main.append("  have hRpow : ∀ j, j < 10 → (aeval x P1)^j = aeval x (Rfun j) := by")
main.append("    intro j hj")
main.append("    interval_cases j")
for j in range(10):
    main.append(f"    · exact hR{j}")
for i in range(1,10):
    main.append(f"""  have hpow{i+1} : x ^ (29 ^ {i+1}) = aeval x P{i+1} := by
    calc
      x ^ (29 ^ {i+1}) = (x ^ (29 ^ {i})) ^ 29 := by
        rw [show 29 ^ {i+1} = 29 ^ {i} * 29 by norm_num, pow_mul]
      _ = (aeval x P{i}) ^ 29 := by rw [hpow{i}]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P{i}).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP{i}deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P{i}).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P{i}).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P{i}).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P{i+1} := by rw [hlin{i}']""")
main.append("""  have hpow10x : x ^ (29 ^ 10) = x := by
    rw [hpow10]
    simp [P10]
  have hdvd : f ∣ (X : (ZMod 29)[X]) ^ (29 ^ 10) - X := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    have : aeval x ((X : (ZMod 29)[X]) ^ (29 ^ 10) - X) = 0 := by
      simpa [map_sub, map_pow, aeval_X, hpow10x]
    exact this
  have hdiv2 : f ∣ (X : (ZMod 29)[X]) ^ (29 ^ 2) - P2 := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    have : aeval x ((X : (ZMod 29)[X]) ^ (29 ^ 2) - P2) = 0 := by
      simpa [map_sub, map_pow, aeval_X, hpow2]
    exact this
  rcases hdiv2 with ⟨q2, hq2⟩
  have hcop2 : IsCoprime f (P2 - X) := by
    refine ⟨A2, B2, ?_⟩
    rw [← hG2]
    exact cert_bez2
  have h2 : IsCoprime f ((X : (ZMod 29)[X]) ^ (29 ^ 2) - X) := by
    have hEq : (X : (ZMod 29)[X]) ^ (29 ^ 2) - X = (P2 - X) + f * q2 := by
      rw [← hq2]
      ring
    rw [hEq]
    exact hcop2.add_mul_left_right q2
  have hdiv5 : f ∣ (X : (ZMod 29)[X]) ^ (29 ^ 5) - P5 := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    have : aeval x ((X : (ZMod 29)[X]) ^ (29 ^ 5) - P5) = 0 := by
      simpa [map_sub, map_pow, aeval_X, hpow5]
    exact this
  rcases hdiv5 with ⟨q5, hq5⟩
  have hcop5 : IsCoprime f (P5 - X) := by
    refine ⟨A5, B5, ?_⟩
    rw [← hG5]
    exact cert_bez5
  have h5 : IsCoprime f ((X : (ZMod 29)[X]) ^ (29 ^ 5) - X) := by
    have hEq : (X : (ZMod 29)[X]) ^ (29 ^ 5) - X = (P5 - X) + f * q5 := by
      rw [← hq5]
      ring
    rw [hEq]
    exact hcop5.add_mul_left_right q5
  exact irreducible_of_degree_ten hfmonic hfdeg
    (by simpa [Nat.card_zmod] using hdvd)
    (by simpa [Nat.card_zmod] using h2)
    (by simpa [Nat.card_zmod] using h5)""")

header="""import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

"""
content=header+defs()+"\n\n"+"\n\n".join(deg_lines)+"\n\n"+"\n\n".join(conv_lines)+"\n\n"+general+"\n\n"+"\n".join(main)+"\n"
open('tmp/sheaf/xif/paper/_S2094gen_final.lean','w',encoding='utf-8').write(content)
print('wrote',len(content))
