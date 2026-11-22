import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2571Bezout5Actual

def A5 : (ZMod 1249)[X] := C 1015 + C 207 * X + C 907 * X ^ 2 + C 672 * X ^ 3 + C 428 * X ^ 4 + C 518 * X ^ 5 + C 1107 * X ^ 6 + C 1199 * X ^ 7 + C 1182 * X ^ 8
def B5 : (ZMod 1249)[X] := C 916 + C 757 * X + C 62 * X ^ 2 + C 823 * X ^ 3 + C 924 * X ^ 4 + C 760 * X ^ 5 + C 650 * X ^ 6 + C 1050 * X ^ 7 + C 403 * X ^ 8 + C 894 * X ^ 9
def S5 : (ZMod 1249)[X] := C 1194 + C 809 * X + C 856 * X ^ 2 + C 203 * X ^ 3 + C 881 * X ^ 4 + C 314 * X ^ 5 + C 738 * X ^ 6 + C 1237 * X ^ 7 + C 176 * X ^ 8 + C 1189 * X ^ 9
def F10 : (ZMod 1249)[X] := S2550F10
def Bez5 : (ZMod 1249)[X] := A5 * F10 + B5 * S5

theorem bezout5 : Bez5 = 1 := by
  have hA : A5.natDegree ≤ 8 := by unfold A5; compute_degree!
  have hB : B5.natDegree ≤ 9 := by unfold B5; compute_degree!
  have hF : F10.natDegree ≤ 10 := by unfold F10 S2550F10; compute_degree!
  have hS : S5.natDegree ≤ 9 := by unfold S5; compute_degree!
  have h1 : (A5 * F10).natDegree ≤ 18 := by
    calc (A5 * F10).natDegree ≤ A5.natDegree + F10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h2 : (B5 * S5).natDegree ≤ 18 := by
    calc (B5 * S5).natDegree ≤ B5.natDegree + S5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hL : Bez5.natDegree ≤ 18 := by
    unfold Bez5
    calc (A5 * F10 + B5 * S5).natDegree
        ≤ max (A5 * F10).natDegree (B5 * S5).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 h2
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Bez5, A5, B5, S5, F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    have hn0 : n ≠ 0 := by omega
    simp [Polynomial.coeff_one, hn0]

theorem R10_eq_X : C (-1248 : ZMod 1249) * X = X := by
  have h : (-1248 : ZMod 1249) = 1 := by decide
  rw [h, C_1, one_mul]

end LeanFormal.IUT.XiFPaper.S2571Bezout5Actual

end