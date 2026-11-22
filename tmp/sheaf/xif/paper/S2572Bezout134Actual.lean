import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2572Bezout134Actual

def F10 : (ZMod 1249)[X] := S2550F10

def A1 : (ZMod 1249)[X] := C 363 + C 394 * X + C 795 * X ^ 2 + C 479 * X ^ 3 + C 872 * X ^ 4 + C 68 * X ^ 5 + C 341 * X ^ 6 + C 532 * X ^ 7 + C 1165 * X ^ 8
def B1 : (ZMod 1249)[X] := C 334 + C 1035 * X + C 1225 * X ^ 2 + C 1064 * X ^ 3 + C 1232 * X ^ 4 + C 780 * X ^ 5 + C 143 * X ^ 6 + C 751 * X ^ 7 + C 936 * X ^ 8 + C 626 * X ^ 9
def S1 : (ZMod 1249)[X] := C 1116 + C 1077 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
def Bez1 : (ZMod 1249)[X] := A1 * F10 + B1 * S1

theorem bezout1 : Bez1 = 1 := by
  have hA : A1.natDegree ≤ 8 := by unfold A1; compute_degree!
  have hB : B1.natDegree ≤ 9 := by unfold B1; compute_degree!
  have hF : F10.natDegree ≤ 10 := by unfold F10 S2550F10; compute_degree!
  have hS : S1.natDegree ≤ 9 := by unfold S1; compute_degree!
  have h1 : (A1 * F10).natDegree ≤ 18 := by
    calc (A1 * F10).natDegree ≤ A1.natDegree + F10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h2 : (B1 * S1).natDegree ≤ 18 := by
    calc (B1 * S1).natDegree ≤ B1.natDegree + S1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hL : Bez1.natDegree ≤ 18 := by
    unfold Bez1
    calc (A1 * F10 + B1 * S1).natDegree
        ≤ max (A1 * F10).natDegree (B1 * S1).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 h2
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Bez1, A1, B1, S1, F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    have hn0 : n ≠ 0 := by omega
    simp [Polynomial.coeff_one, hn0]

def A3 : (ZMod 1249)[X] := C 652 + C 551 * X + C 473 * X ^ 2 + C 305 * X ^ 3 + C 216 * X ^ 4 + C 298 * X ^ 5 + C 1019 * X ^ 6 + C 257 * X ^ 7 + C 1095 * X ^ 8
def B3 : (ZMod 1249)[X] := C 455 + C 635 * X + C 679 * X ^ 2 + C 837 * X ^ 3 + C 193 * X ^ 4 + C 404 * X ^ 5 + C 229 * X ^ 6 + C 603 * X ^ 7 + C 619 * X ^ 8 + C 284 * X ^ 9
def S3 : (ZMod 1249)[X] := C 352 + C 512 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
def Bez3 : (ZMod 1249)[X] := A3 * F10 + B3 * S3

theorem bezout3 : Bez3 = 1 := by
  have hA : A3.natDegree ≤ 8 := by unfold A3; compute_degree!
  have hB : B3.natDegree ≤ 9 := by unfold B3; compute_degree!
  have hF : F10.natDegree ≤ 10 := by unfold F10 S2550F10; compute_degree!
  have hS : S3.natDegree ≤ 9 := by unfold S3; compute_degree!
  have h1 : (A3 * F10).natDegree ≤ 18 := by
    calc (A3 * F10).natDegree ≤ A3.natDegree + F10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h2 : (B3 * S3).natDegree ≤ 18 := by
    calc (B3 * S3).natDegree ≤ B3.natDegree + S3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hL : Bez3.natDegree ≤ 18 := by
    unfold Bez3
    calc (A3 * F10 + B3 * S3).natDegree
        ≤ max (A3 * F10).natDegree (B3 * S3).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 h2
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Bez3, A3, B3, S3, F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    have hn0 : n ≠ 0 := by omega
    simp [Polynomial.coeff_one, hn0]

def A4 : (ZMod 1249)[X] := C 738 + C 77 * X + C 333 * X ^ 2 + C 827 * X ^ 3 + C 1126 * X ^ 4 + C 788 * X ^ 5 + C 560 * X ^ 6 + C 1163 * X ^ 7 + C 1035 * X ^ 8
def B4 : (ZMod 1249)[X] := C 961 + C 156 * X + C 697 * X ^ 2 + C 937 * X ^ 3 + C 647 * X ^ 4 + C 561 * X ^ 5 + C 1121 * X ^ 6 + C 41 * X ^ 7 + C 1218 * X ^ 8 + C 237 * X ^ 9
def S4 : (ZMod 1249)[X] := C 762 + C 334 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
def Bez4 : (ZMod 1249)[X] := A4 * F10 + B4 * S4

theorem bezout4 : Bez4 = 1 := by
  have hA : A4.natDegree ≤ 8 := by unfold A4; compute_degree!
  have hB : B4.natDegree ≤ 9 := by unfold B4; compute_degree!
  have hF : F10.natDegree ≤ 10 := by unfold F10 S2550F10; compute_degree!
  have hS : S4.natDegree ≤ 9 := by unfold S4; compute_degree!
  have h1 : (A4 * F10).natDegree ≤ 18 := by
    calc (A4 * F10).natDegree ≤ A4.natDegree + F10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h2 : (B4 * S4).natDegree ≤ 18 := by
    calc (B4 * S4).natDegree ≤ B4.natDegree + S4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hL : Bez4.natDegree ≤ 18 := by
    unfold Bez4
    calc (A4 * F10 + B4 * S4).natDegree
        ≤ max (A4 * F10).natDegree (B4 * S4).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 h2
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Bez4, A4, B4, S4, F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    have hn0 : n ≠ 0 := by omega
    simp [Polynomial.coeff_one, hn0]

end LeanFormal.IUT.XiFPaper.S2572Bezout134Actual

end