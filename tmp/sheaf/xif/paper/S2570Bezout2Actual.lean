import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2570Bezout2Actual

def A2 : (ZMod 1249)[X] := C 674 + C 1117 * X + C 222 * X ^ 2 + C 503 * X ^ 3 + C 799 * X ^ 4 + C 642 * X ^ 5 + C 379 * X ^ 6 + C 271 * X ^ 7 + C 440 * X ^ 8
def B2 : (ZMod 1249)[X] := C 1130 + C 94 * X + C 731 * X ^ 2 + C 910 * X ^ 3 + C 431 * X ^ 4 + C 498 * X ^ 5 + C 677 * X ^ 6 + C 780 * X ^ 7 + C 275 * X ^ 8 + C 662 * X ^ 9
def S2 : (ZMod 1249)[X] := C 871 + C 628 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
def F10 : (ZMod 1249)[X] := S2550F10
def Bez : (ZMod 1249)[X] := A2 * F10 + B2 * S2

theorem bezout2 : Bez = 1 := by
  have hA : A2.natDegree ≤ 8 := by unfold A2; compute_degree!
  have hB : B2.natDegree ≤ 9 := by unfold B2; compute_degree!
  have hF : F10.natDegree ≤ 10 := by unfold F10 S2550F10; compute_degree!
  have hS : S2.natDegree ≤ 9 := by unfold S2; compute_degree!
  have h1 : (A2 * F10).natDegree ≤ 18 := by
    calc (A2 * F10).natDegree ≤ A2.natDegree + F10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h2 : (B2 * S2).natDegree ≤ 18 := by
    calc (B2 * S2).natDegree ≤ B2.natDegree + S2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hL : Bez.natDegree ≤ 18 := by
    unfold Bez
    calc (A2 * F10 + B2 * S2).natDegree
        ≤ max (A2 * F10).natDegree (B2 * S2).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 h2
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Bez, A2, B2, S2, F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    have hn0 : n ≠ 0 := by omega
    simp [Polynomial.coeff_one, hn0]

end LeanFormal.IUT.XiFPaper.S2570Bezout2Actual

end