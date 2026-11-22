import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

def R0 : (ZMod 1249)[X] := C 1 * X
def R1 : (ZMod 1249)[X] := C 1 * X ^ 2
def R2 : (ZMod 1249)[X] := C 1 * X ^ 4
def R3 : (ZMod 1249)[X] := C 1 * X ^ 8
def R4 : (ZMod 1249)[X] := C 1027 + C 709 * X + C 230 * X ^ 2 + C 1087 * X ^ 3 + C 1102 * X ^ 4 + C 35 * X ^ 5 + C 677 * X ^ 6 + C 155 * X ^ 7 + C 300 * X ^ 8 + C 912 * X ^ 9
def R5 : (ZMod 1249)[X] := C 1060 + C 957 * X + C 591 * X ^ 2 + C 766 * X ^ 3 + C 816 * X ^ 4 + C 315 * X ^ 5 + C 752 * X ^ 6 + C 499 * X ^ 7 + C 317 * X ^ 8 + C 847 * X ^ 9
def R6 : (ZMod 1249)[X] := C 317 + C 512 * X + C 819 * X ^ 2 + C 1154 * X ^ 3 + C 767 * X ^ 4 + C 1060 * X ^ 5 + C 1110 * X ^ 6 + C 701 * X ^ 7 + C 571 * X ^ 8 + C 172 * X ^ 9
def R7 : (ZMod 1249)[X] := C 933 + C 976 * X + C 1083 * X ^ 2 + C 1020 * X ^ 3 + C 954 * X ^ 4 + C 30 * X ^ 5 + C 223 * X ^ 6 + C 46 * X ^ 7 + C 498 * X ^ 8 + C 892 * X ^ 9
def R8 : (ZMod 1249)[X] := C 921 + C 377 * X + C 428 * X ^ 2 + C 159 * X ^ 3 + C 1034 * X ^ 4 + C 640 * X ^ 5 + C 1087 * X ^ 6 + C 395 * X ^ 7 + C 249 * X ^ 8 + C 1181 * X ^ 9
def R9 : (ZMod 1249)[X] := C 666 + C 125 * X + C 73 * X ^ 2 + C 778 * X ^ 3 + C 1015 * X ^ 4 + C 917 * X ^ 5 + C 952 * X ^ 6 + C 978 * X ^ 7 + C 38 * X ^ 8 + C 388 * X ^ 9
def R10 : (ZMod 1249)[X] := C 91 + C 1214 * X + C 319 * X ^ 2 + C 805 * X ^ 3 + C 483 * X ^ 4 + C 435 * X ^ 5 + C 1242 * X ^ 6 + C 371 * X ^ 7 + C 124 * X ^ 8 + C 193 * X ^ 9
def Q0 : (ZMod 1249)[X] := 0
def Q1 : (ZMod 1249)[X] := 0
def Q2 : (ZMod 1249)[X] := 0
def Q3 : (ZMod 1249)[X] := C 823 + C 588 * X + C 967 * X ^ 2 + C 13 * X ^ 3 + C 592 * X ^ 4 + C 679 * X ^ 5 + C 1 * X ^ 6
def Q4 : (ZMod 1249)[X] := C 867 + C 15 * X + C 760 * X ^ 2 + C 406 * X ^ 3 + C 464 * X ^ 4 + C 255 * X ^ 5 + C 972 * X ^ 6 + C 229 * X ^ 7 + C 1159 * X ^ 8
def Q5 : (ZMod 1249)[X] := C 285 + C 138 * X + C 1169 * X ^ 2 + C 1206 * X ^ 3 + C 296 * X ^ 4 + C 375 * X ^ 5 + C 40 * X ^ 6 + C 647 * X ^ 7 + C 483 * X ^ 8
def Q6 : (ZMod 1249)[X] := C 766 + C 244 * X + C 926 * X ^ 2 + C 359 * X ^ 3 + C 316 * X ^ 4 + C 44 * X ^ 5 + C 318 * X ^ 6 + C 200 * X ^ 7 + C 857 * X ^ 8
def Q7 : (ZMod 1249)[X] := C 1215 + C 1239 * X + C 880 * X ^ 2 + C 1214 * X ^ 3 + C 1061 * X ^ 4 + C 617 * X ^ 5 + C 109 * X ^ 6 + C 50 * X ^ 7 + C 51 * X ^ 8
def Q8 : (ZMod 1249)[X] := C 783 + C 889 * X + C 1053 * X ^ 2 + C 676 * X ^ 3 + C 1213 * X ^ 4 + C 339 * X ^ 5 + C 821 * X ^ 6 + C 818 * X ^ 7 + C 877 * X ^ 8
def Q9 : (ZMod 1249)[X] := C 237 + C 1001 * X + C 601 * X ^ 2 + C 854 * X ^ 3 + C 787 * X ^ 4 + C 445 * X ^ 5 + C 266 * X ^ 6 + C 728 * X ^ 7 + C 664 * X ^ 8

theorem step0 : R0 * R0 = S2550F10 * Q0 + R1 := by
  have hRk : R0.natDegree ≤ 9 := by unfold R0; compute_degree!
  have hQ : Q0.natDegree ≤ 8 := by unfold Q0; compute_degree!
  have hRn : R1.natDegree ≤ 9 := by unfold R1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R0 * R0).natDegree ≤ 18 := by
    calc (R0 * R0).natDegree ≤ R0.natDegree + R0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q0).natDegree ≤ 18 := by
    calc (S2550F10 * Q0).natDegree ≤ S2550F10.natDegree + Q0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q0 + R1).natDegree ≤ 18 := by
    calc (S2550F10 * Q0 + R1).natDegree
        ≤ max (S2550F10 * Q0).natDegree R1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R0, Q0, R1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step1 : R1 * R1 = S2550F10 * Q1 + R2 := by
  have hRk : R1.natDegree ≤ 9 := by unfold R1; compute_degree!
  have hQ : Q1.natDegree ≤ 8 := by unfold Q1; compute_degree!
  have hRn : R2.natDegree ≤ 9 := by unfold R2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R1 * R1).natDegree ≤ 18 := by
    calc (R1 * R1).natDegree ≤ R1.natDegree + R1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q1).natDegree ≤ 18 := by
    calc (S2550F10 * Q1).natDegree ≤ S2550F10.natDegree + Q1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q1 + R2).natDegree ≤ 18 := by
    calc (S2550F10 * Q1 + R2).natDegree
        ≤ max (S2550F10 * Q1).natDegree R2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R1, Q1, R2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step2 : R2 * R2 = S2550F10 * Q2 + R3 := by
  have hRk : R2.natDegree ≤ 9 := by unfold R2; compute_degree!
  have hQ : Q2.natDegree ≤ 8 := by unfold Q2; compute_degree!
  have hRn : R3.natDegree ≤ 9 := by unfold R3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R2 * R2).natDegree ≤ 18 := by
    calc (R2 * R2).natDegree ≤ R2.natDegree + R2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q2).natDegree ≤ 18 := by
    calc (S2550F10 * Q2).natDegree ≤ S2550F10.natDegree + Q2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q2 + R3).natDegree ≤ 18 := by
    calc (S2550F10 * Q2 + R3).natDegree
        ≤ max (S2550F10 * Q2).natDegree R3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R2, Q2, R3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step3 : R3 * R3 = S2550F10 * Q3 + R4 := by
  have hRk : R3.natDegree ≤ 9 := by unfold R3; compute_degree!
  have hQ : Q3.natDegree ≤ 8 := by unfold Q3; compute_degree!
  have hRn : R4.natDegree ≤ 9 := by unfold R4; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R3 * R3).natDegree ≤ 18 := by
    calc (R3 * R3).natDegree ≤ R3.natDegree + R3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q3).natDegree ≤ 18 := by
    calc (S2550F10 * Q3).natDegree ≤ S2550F10.natDegree + Q3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q3 + R4).natDegree ≤ 18 := by
    calc (S2550F10 * Q3 + R4).natDegree
        ≤ max (S2550F10 * Q3).natDegree R4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R3, Q3, R4, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step4 : R4 * R4 = S2550F10 * Q4 + R5 := by
  have hRk : R4.natDegree ≤ 9 := by unfold R4; compute_degree!
  have hQ : Q4.natDegree ≤ 8 := by unfold Q4; compute_degree!
  have hRn : R5.natDegree ≤ 9 := by unfold R5; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R4 * R4).natDegree ≤ 18 := by
    calc (R4 * R4).natDegree ≤ R4.natDegree + R4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q4).natDegree ≤ 18 := by
    calc (S2550F10 * Q4).natDegree ≤ S2550F10.natDegree + Q4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q4 + R5).natDegree ≤ 18 := by
    calc (S2550F10 * Q4 + R5).natDegree
        ≤ max (S2550F10 * Q4).natDegree R5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R4, Q4, R5, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step5 : R5 * R5 = S2550F10 * Q5 + R6 := by
  have hRk : R5.natDegree ≤ 9 := by unfold R5; compute_degree!
  have hQ : Q5.natDegree ≤ 8 := by unfold Q5; compute_degree!
  have hRn : R6.natDegree ≤ 9 := by unfold R6; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R5 * R5).natDegree ≤ 18 := by
    calc (R5 * R5).natDegree ≤ R5.natDegree + R5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q5).natDegree ≤ 18 := by
    calc (S2550F10 * Q5).natDegree ≤ S2550F10.natDegree + Q5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q5 + R6).natDegree ≤ 18 := by
    calc (S2550F10 * Q5 + R6).natDegree
        ≤ max (S2550F10 * Q5).natDegree R6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R5, Q5, R6, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step6 : R6 * R6 = S2550F10 * Q6 + R7 := by
  have hRk : R6.natDegree ≤ 9 := by unfold R6; compute_degree!
  have hQ : Q6.natDegree ≤ 8 := by unfold Q6; compute_degree!
  have hRn : R7.natDegree ≤ 9 := by unfold R7; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R6 * R6).natDegree ≤ 18 := by
    calc (R6 * R6).natDegree ≤ R6.natDegree + R6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q6).natDegree ≤ 18 := by
    calc (S2550F10 * Q6).natDegree ≤ S2550F10.natDegree + Q6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q6 + R7).natDegree ≤ 18 := by
    calc (S2550F10 * Q6 + R7).natDegree
        ≤ max (S2550F10 * Q6).natDegree R7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R6, Q6, R7, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step7 : R7 * R7 = S2550F10 * Q7 + R8 := by
  have hRk : R7.natDegree ≤ 9 := by unfold R7; compute_degree!
  have hQ : Q7.natDegree ≤ 8 := by unfold Q7; compute_degree!
  have hRn : R8.natDegree ≤ 9 := by unfold R8; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R7 * R7).natDegree ≤ 18 := by
    calc (R7 * R7).natDegree ≤ R7.natDegree + R7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q7).natDegree ≤ 18 := by
    calc (S2550F10 * Q7).natDegree ≤ S2550F10.natDegree + Q7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q7 + R8).natDegree ≤ 18 := by
    calc (S2550F10 * Q7 + R8).natDegree
        ≤ max (S2550F10 * Q7).natDegree R8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R7, Q7, R8, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step8 : R8 * R8 = S2550F10 * Q8 + R9 := by
  have hRk : R8.natDegree ≤ 9 := by unfold R8; compute_degree!
  have hQ : Q8.natDegree ≤ 8 := by unfold Q8; compute_degree!
  have hRn : R9.natDegree ≤ 9 := by unfold R9; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R8 * R8).natDegree ≤ 18 := by
    calc (R8 * R8).natDegree ≤ R8.natDegree + R8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q8).natDegree ≤ 18 := by
    calc (S2550F10 * Q8).natDegree ≤ S2550F10.natDegree + Q8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q8 + R9).natDegree ≤ 18 := by
    calc (S2550F10 * Q8 + R9).natDegree
        ≤ max (S2550F10 * Q8).natDegree R9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R8, Q8, R9, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

theorem step9 : R9 * R9 = S2550F10 * Q9 + R10 := by
  have hRk : R9.natDegree ≤ 9 := by unfold R9; compute_degree!
  have hQ : Q9.natDegree ≤ 8 := by unfold Q9; compute_degree!
  have hRn : R10.natDegree ≤ 9 := by unfold R10; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (R9 * R9).natDegree ≤ 18 := by
    calc (R9 * R9).natDegree ≤ R9.natDegree + R9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Q9).natDegree ≤ 18 := by
    calc (S2550F10 * Q9).natDegree ≤ S2550F10.natDegree + Q9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Q9 + R10).natDegree ≤ 18 := by
    calc (S2550F10 * Q9 + R10).natDegree
        ≤ max (S2550F10 * Q9).natDegree R10.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [R9, Q9, R10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

end