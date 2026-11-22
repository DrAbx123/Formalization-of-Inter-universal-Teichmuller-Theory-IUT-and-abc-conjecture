import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2560Batch1Actual

def R0 : (ZMod 1249)[X] := X * 1
def R1 : (ZMod 1249)[X] := X ^ 2 * 1
def R2 : (ZMod 1249)[X] := X ^ 4 * 1
def R3 : (ZMod 1249)[X] := X ^ 8 * 1
def R4 : (ZMod 1249)[X] := 1027 + X * 709 + X ^ 2 * 230 + X ^ 3 * 1087 + X ^ 4 * 1102 + X ^ 5 * 35 + X ^ 6 * 677 + X ^ 7 * 155 + X ^ 8 * 300 + X ^ 9 * 912
def R5 : (ZMod 1249)[X] := 1060 + X * 957 + X ^ 2 * 591 + X ^ 3 * 766 + X ^ 4 * 816 + X ^ 5 * 315 + X ^ 6 * 752 + X ^ 7 * 499 + X ^ 8 * 317 + X ^ 9 * 847
def R6 : (ZMod 1249)[X] := 317 + X * 512 + X ^ 2 * 819 + X ^ 3 * 1154 + X ^ 4 * 767 + X ^ 5 * 1060 + X ^ 6 * 1110 + X ^ 7 * 701 + X ^ 8 * 571 + X ^ 9 * 172
def R7 : (ZMod 1249)[X] := 933 + X * 976 + X ^ 2 * 1083 + X ^ 3 * 1020 + X ^ 4 * 954 + X ^ 5 * 30 + X ^ 6 * 223 + X ^ 7 * 46 + X ^ 8 * 498 + X ^ 9 * 892
def R8 : (ZMod 1249)[X] := 921 + X * 377 + X ^ 2 * 428 + X ^ 3 * 159 + X ^ 4 * 1034 + X ^ 5 * 640 + X ^ 6 * 1087 + X ^ 7 * 395 + X ^ 8 * 249 + X ^ 9 * 1181
def R9 : (ZMod 1249)[X] := 666 + X * 125 + X ^ 2 * 73 + X ^ 3 * 778 + X ^ 4 * 1015 + X ^ 5 * 917 + X ^ 6 * 952 + X ^ 7 * 978 + X ^ 8 * 38 + X ^ 9 * 388
def R10 : (ZMod 1249)[X] := 91 + X * 1214 + X ^ 2 * 319 + X ^ 3 * 805 + X ^ 4 * 483 + X ^ 5 * 435 + X ^ 6 * 1242 + X ^ 7 * 371 + X ^ 8 * 124 + X ^ 9 * 193

def L0 : (ZMod 1249)[X] := X ^ 2 * 1
def M0 : (ZMod 1249)[X] := X ^ 2 * 1
theorem step0 : L0 = M0 := by
  have hL : L0.natDegree ≤ 18 := by unfold L0; compute_degree!
  have hR : M0.natDegree ≤ 18 := by unfold M0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L0, M0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L1 : (ZMod 1249)[X] := X ^ 4 * 1
def M1 : (ZMod 1249)[X] := X ^ 4 * 1
theorem step1 : L1 = M1 := by
  have hL : L1.natDegree ≤ 18 := by unfold L1; compute_degree!
  have hR : M1.natDegree ≤ 18 := by unfold M1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L1, M1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L2 : (ZMod 1249)[X] := X ^ 8 * 1
def M2 : (ZMod 1249)[X] := X ^ 8 * 1
theorem step2 : L2 = M2 := by
  have hL : L2.natDegree ≤ 18 := by unfold L2; compute_degree!
  have hR : M2.natDegree ≤ 18 := by unfold M2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L2, M2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L3 : (ZMod 1249)[X] := X ^ 16 * 1
def M3 : (ZMod 1249)[X] := X ^ 16 * 1
theorem step3 : L3 = M3 := by
  have hL : L3.natDegree ≤ 18 := by unfold L3; compute_degree!
  have hR : M3.natDegree ≤ 18 := by unfold M3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L3, M3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L4 : (ZMod 1249)[X] := 573 + X * 1201 + X ^ 2 * 881 + X ^ 3 * 886 + X ^ 4 * 862 + X ^ 5 * 5 + X ^ 6 * 1181 + X ^ 7 * 658 + X ^ 8 * 1105 + X ^ 9 * 773 + X ^ 10 * 380 + X ^ 11 * 649 + X ^ 12 * 559 + X ^ 13 * 212 + X ^ 14 * 710 + X ^ 15 * 161 + X ^ 16 * 518 + X ^ 17 * 138 + X ^ 18 * 1159
def M4 : (ZMod 1249)[X] := 573 + X * 1201 + X ^ 2 * 881 + X ^ 3 * 886 + X ^ 4 * 862 + X ^ 5 * 5 + X ^ 6 * 1181 + X ^ 7 * 658 + X ^ 8 * 1105 + X ^ 9 * 773 + X ^ 10 * 380 + X ^ 11 * 649 + X ^ 12 * 559 + X ^ 13 * 212 + X ^ 14 * 710 + X ^ 15 * 161 + X ^ 16 * 518 + X ^ 17 * 138 + X ^ 18 * 1159
theorem step4 : L4 = M4 := by
  have hL : L4.natDegree ≤ 18 := by unfold L4; compute_degree!
  have hR : M4.natDegree ≤ 18 := by unfold M4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L4, M4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L5 : (ZMod 1249)[X] := 749 + X * 464 + X ^ 2 * 505 + X ^ 3 * 1049 + X ^ 4 * 663 + X ^ 5 * 46 + X ^ 6 * 169 + X ^ 7 * 448 + X ^ 8 * 1109 + X ^ 9 * 819 + X ^ 10 * 81 + X ^ 11 * 897 + X ^ 12 * 729 + X ^ 13 * 627 + X ^ 14 * 387 + X ^ 15 * 277 + X ^ 16 * 302 + X ^ 17 * 1177 + X ^ 18 * 483
def M5 : (ZMod 1249)[X] := 749 + X * 464 + X ^ 2 * 505 + X ^ 3 * 1049 + X ^ 4 * 663 + X ^ 5 * 46 + X ^ 6 * 169 + X ^ 7 * 448 + X ^ 8 * 1109 + X ^ 9 * 819 + X ^ 10 * 81 + X ^ 11 * 897 + X ^ 12 * 729 + X ^ 13 * 627 + X ^ 14 * 387 + X ^ 15 * 277 + X ^ 16 * 302 + X ^ 17 * 1177 + X ^ 18 * 483
theorem step5 : L5 = M5 := by
  have hL : L5.natDegree ≤ 18 := by unfold L5; compute_degree!
  have hR : M5.natDegree ≤ 18 := by unfold M5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L5, M5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L6 : (ZMod 1249)[X] := 569 + X * 1117 + X ^ 2 * 765 + X ^ 3 * 299 + X ^ 4 * 607 + X ^ 5 * 380 + X ^ 6 * 746 + X ^ 7 * 413 + X ^ 8 * 37 + X ^ 9 * 987 + X ^ 10 * 122 + X ^ 11 * 913 + X ^ 12 * 555 + X ^ 13 * 514 + X ^ 14 * 361 + X ^ 15 * 828 + X ^ 16 * 139 + X ^ 17 * 331 + X ^ 18 * 857
def M6 : (ZMod 1249)[X] := 569 + X * 1117 + X ^ 2 * 765 + X ^ 3 * 299 + X ^ 4 * 607 + X ^ 5 * 380 + X ^ 6 * 746 + X ^ 7 * 413 + X ^ 8 * 37 + X ^ 9 * 987 + X ^ 10 * 122 + X ^ 11 * 913 + X ^ 12 * 555 + X ^ 13 * 514 + X ^ 14 * 361 + X ^ 15 * 828 + X ^ 16 * 139 + X ^ 17 * 331 + X ^ 18 * 857
theorem step6 : L6 = M6 := by
  have hL : L6.natDegree ≤ 18 := by unfold L6; compute_degree!
  have hR : M6.natDegree ≤ 18 := by unfold M6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L6, M6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L7 : (ZMod 1249)[X] := 1185 + X * 174 + X ^ 2 * 834 + X ^ 3 * 552 + X ^ 4 * 551 + X ^ 5 * 812 + X ^ 6 * 559 + X ^ 7 * 549 + X ^ 8 * 374 + X ^ 9 * 964 + X ^ 10 * 250 + X ^ 11 * 331 + X ^ 12 * 862 + X ^ 13 * 1234 + X ^ 14 * 466 + X ^ 15 * 253 + X ^ 16 * 332 + X ^ 17 * 393 + X ^ 18 * 51
def M7 : (ZMod 1249)[X] := 1185 + X * 174 + X ^ 2 * 834 + X ^ 3 * 552 + X ^ 4 * 551 + X ^ 5 * 812 + X ^ 6 * 559 + X ^ 7 * 549 + X ^ 8 * 374 + X ^ 9 * 964 + X ^ 10 * 250 + X ^ 11 * 331 + X ^ 12 * 862 + X ^ 13 * 1234 + X ^ 14 * 466 + X ^ 15 * 253 + X ^ 16 * 332 + X ^ 17 * 393 + X ^ 18 * 51
theorem step7 : L7 = M7 := by
  have hL : L7.natDegree ≤ 18 := by unfold L7; compute_degree!
  have hR : M7.natDegree ≤ 18 := by unfold M7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L7, M7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L8 : (ZMod 1249)[X] := 170 + X * 1239 + X ^ 3 * 1082 + X ^ 4 * 715 + X ^ 5 * 47 + X ^ 6 * 417 + X ^ 7 * 780 + X ^ 8 * 755 + X ^ 9 * 203 + X ^ 10 * 1105 + X ^ 11 * 978 + X ^ 12 * 972 + X ^ 13 * 156 + X ^ 14 * 799 + X ^ 15 * 167 + X ^ 16 * 787 + X ^ 17 * 1108 + X ^ 18 * 877
def M8 : (ZMod 1249)[X] := 170 + X * 1239 + X ^ 3 * 1082 + X ^ 4 * 715 + X ^ 5 * 47 + X ^ 6 * 417 + X ^ 7 * 780 + X ^ 8 * 755 + X ^ 9 * 203 + X ^ 10 * 1105 + X ^ 11 * 978 + X ^ 12 * 972 + X ^ 13 * 156 + X ^ 14 * 799 + X ^ 15 * 167 + X ^ 16 * 787 + X ^ 17 * 1108 + X ^ 18 * 877
theorem step8 : L8 = M8 := by
  have hL : L8.natDegree ≤ 18 := by unfold L8; compute_degree!
  have hR : M8.natDegree ≤ 18 := by unfold M8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L8, M8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def L9 : (ZMod 1249)[X] := 161 + X * 383 + X ^ 2 * 451 + X ^ 3 * 390 + X ^ 4 * 551 + X ^ 5 * 54 + X ^ 6 * 90 + X ^ 7 * 273 + X ^ 8 * 999 + X ^ 9 * 138 + X ^ 10 * 36 + X ^ 11 * 164 + X ^ 12 * 1030 + X ^ 13 * 371 + X ^ 14 * 571 + X ^ 15 * 1230 + X ^ 16 * 980 + X ^ 17 * 761 + X ^ 18 * 664
def M9 : (ZMod 1249)[X] := 161 + X * 383 + X ^ 2 * 451 + X ^ 3 * 390 + X ^ 4 * 551 + X ^ 5 * 54 + X ^ 6 * 90 + X ^ 7 * 273 + X ^ 8 * 999 + X ^ 9 * 138 + X ^ 10 * 36 + X ^ 11 * 164 + X ^ 12 * 1030 + X ^ 13 * 371 + X ^ 14 * 571 + X ^ 15 * 1230 + X ^ 16 * 980 + X ^ 17 * 761 + X ^ 18 * 664
theorem step9 : L9 = M9 := by
  have hL : L9.natDegree ≤ 18 := by unfold L9; compute_degree!
  have hR : M9.natDegree ≤ 18 := by unfold M9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L9, M9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2560Batch1Actual

end