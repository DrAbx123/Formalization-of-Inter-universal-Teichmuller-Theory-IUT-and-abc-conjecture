import tmp.sheaf.xif.paper.S2550Mod13IrreducibleActual
noncomputable section
set_option maxHeartbeats 8000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2551Mod13DataActualAdapted
open LeanFormal.IUT.XiFPaper.S2550Mod13IrreducibleActual
def G : (ZMod 13)[X] :=
  C 5 + C 11 * X ^ 2 + C 5 * X ^ 3 + C 2 * X ^ 4 + C 5 * X ^ 5 + C 2 * X ^ 7 + C 8 * X ^ 8 + C 5 * X ^ 9 + C 10 * X ^ 10 + C 3 * X ^ 11 + C 1 * X ^ 12

def T1 : (ZMod 13)[X] :=
  C 2 + C 8 * X + C 7 * X ^ 2 + C 4 * X ^ 3 + C 1 * X ^ 4 + C 8 * X ^ 6 + C 6 * X ^ 7 + C 9 * X ^ 8 + C 7 * X ^ 9 + C 12 * X ^ 10 + C 12 * X ^ 11

def T2 : (ZMod 13)[X] :=
  C 9 + C 12 * X + C 9 * X ^ 2 + C 12 * X ^ 3 + C 4 * X ^ 4 + C 8 * X ^ 5 + C 2 * X ^ 6 + C 8 * X ^ 7 + C 9 * X ^ 8 + C 12 * X ^ 9 + C 9 * X ^ 10 + C 4 * X ^ 11

def T3 : (ZMod 13)[X] :=
  C 2 + C 2 * X + C 10 * X ^ 2 + C 11 * X ^ 3 + C 9 * X ^ 4 + C 4 * X ^ 5 + C 6 * X ^ 6 + C 6 * X ^ 7 + C 12 * X ^ 8 + C 1 * X ^ 9 + C 2 * X ^ 10 + C 10 * X ^ 11

def T4 : (ZMod 13)[X] :=
  C 2 + C 4 * X + C 2 * X ^ 2 + C 9 * X ^ 3 + C 5 * X ^ 4 + C 3 * X ^ 5 + C 12 * X ^ 6 + C 9 * X ^ 7 + C 9 * X ^ 8 + C 4 * X ^ 9 + C 8 * X ^ 10 + C 3 * X ^ 11

def T5 : (ZMod 13)[X] :=
  C 7 + C 5 * X ^ 2 + C 3 * X ^ 3 + C 1 * X ^ 4 + C 10 * X ^ 5 + C 10 * X ^ 6 + C 9 * X ^ 8 + C 5 * X ^ 9 + C 4 * X ^ 10 + C 4 * X ^ 11

def T6 : (ZMod 13)[X] :=
  C 2 + C 5 * X + C 12 * X ^ 2 + C 7 * X ^ 3 + C 6 * X ^ 4 + C 11 * X ^ 5 + C 11 * X ^ 6 + C 6 * X ^ 7 + C 11 * X ^ 8 + C 1 * X ^ 9 + C 5 * X ^ 10 + C 6 * X ^ 11

def T7 : (ZMod 13)[X] :=
  C 4 + C 4 * X + C 5 * X ^ 2 + C 5 * X ^ 3 + C 12 * X ^ 4 + C 11 * X ^ 5 + C 2 * X ^ 6 + C 4 * X ^ 7 + C 3 * X ^ 8 + C 10 * X ^ 11

def T8 : (ZMod 13)[X] :=
  C 2 + C 8 * X + C 7 * X ^ 2 + C 8 * X ^ 3 + C 5 * X ^ 4 + C 8 * X ^ 5 + C 6 * X ^ 6 + C 7 * X ^ 7 + C 2 * X ^ 8 + C 8 * X ^ 10 + C 12 * X ^ 11

def T9 : (ZMod 13)[X] :=
  C 12 + C 11 * X + C 9 * X ^ 2 + C 4 * X ^ 3 + C 4 * X ^ 4 + C 10 * X ^ 5 + C 6 * X ^ 6 + C 11 * X ^ 7 + C 6 * X ^ 8 + C 8 * X ^ 9 + C 9 * X ^ 10 + C 4 * X ^ 11

def T10 : (ZMod 13)[X] :=
  C 12 + C 8 * X + C 4 * X ^ 2 + C 6 * X ^ 5 + C 5 * X ^ 6 + C 2 * X ^ 7 + C 7 * X ^ 8 + C 7 * X ^ 9 + C 11 * X ^ 10 + C 9 * X ^ 11

def T11 : (ZMod 13)[X] :=
  C 8 + C 2 * X + C 8 * X ^ 2 + C 2 * X ^ 3 + C 5 * X ^ 4 + C 7 * X ^ 5 + C 10 * X ^ 6 + C 6 * X ^ 7 + C 1 * X ^ 8 + C 7 * X ^ 9 + C 10 * X ^ 10 + C 4 * X ^ 11

def U4 : (ZMod 13)[X] :=
  C 6 + C 11 * X + C 1 * X ^ 2 + C 11 * X ^ 3 + C 2 * X ^ 4 + C 10 * X ^ 5 + C 7 * X ^ 6 + C 1 * X ^ 7 + C 3 * X ^ 8 + C 1 * X ^ 9 + C 12 * X ^ 10

def V4 : (ZMod 13)[X] :=
  C 2 + C 2 * X + C 5 * X ^ 2 + C 2 * X ^ 3 + C 12 * X ^ 4 + C 11 * X ^ 5 + C 8 * X ^ 7 + C 8 * X ^ 8 + C 1 * X ^ 9 + C 7 * X ^ 10 + C 9 * X ^ 11

def U6 : (ZMod 13)[X] :=
  C 7 + C 3 * X + C 1 * X ^ 2 + C 11 * X ^ 3 + C 11 * X ^ 4 + C 11 * X ^ 5 + C 3 * X ^ 6 + C 7 * X ^ 7 + C 4 * X ^ 8 + C 6 * X ^ 9 + C 1 * X ^ 10

def V6 : (ZMod 13)[X] :=
  C 5 + C 2 * X + C 3 * X ^ 2 + C 7 * X ^ 3 + C 9 * X ^ 4 + C 6 * X ^ 5 + C 5 * X ^ 6 + C 6 * X ^ 7 + C 10 * X ^ 8 + C 6 * X ^ 9 + C 12 * X ^ 10 + C 2 * X ^ 11

theorem G_eq_C_mul_F13 : G = C (8 : ZMod 13) * F13 := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;> (simp [G, F13] <;> decide)
  · have h1 : G.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : G.natDegree ≤ 12 := by unfold G; compute_degree!
      omega
    have h2 : (C (8 : ZMod 13) * F13).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_C_mul (by decide : (8 : ZMod 13) ≠ 0), F13_natDegree]
      omega
    rw [h1, h2]
theorem G_monic : G.Monic := by
  rw [G_eq_C_mul_F13]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  unfold F13
  compute_degree!
  decide
theorem T12_eq_X : T12 = X := by
  ext n
  by_cases hn : n ≤ 1
  · interval_cases n <;> (simp [T12] <;> decide)
  · have h1 : T12.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : T12.natDegree ≤ 1 := by unfold T12; compute_degree!
      omega
    have h2 : (X : (ZMod 13)[X]).coeff n = 0 := by simp [Polynomial.coeff_X, hn]
    rw [h1, h2]
#print axioms G_monic
#print axioms G_eq_C_mul_F13
#print axioms T12_eq_X
end LeanFormal.IUT.XiFPaper.S2551Mod13DataActualAdapted
end
