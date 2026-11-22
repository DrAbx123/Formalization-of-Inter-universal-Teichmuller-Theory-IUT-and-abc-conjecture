import tmp.sheaf.xif.paper.S2562Batch3CorrectActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

def A0 : (ZMod 1249)[X] := C 292 + C 107 * X + C 397 * X ^ 2 + C 634 * X ^ 3 + C 925 * X ^ 4 + C 322 * X ^ 5 + C 524 * X ^ 6 + C 1173 * X ^ 7 + C 157 * X ^ 8 + C 457 * X ^ 9
def A1 : (ZMod 1249)[X] := C 686 + C 832 * X + C 55 * X ^ 2 + C 574 * X ^ 3 + C 937 * X ^ 4 + C 980 * X ^ 5 + C 438 * X ^ 6 + C 1082 * X ^ 7 + C 51 * X ^ 8 + C 600 * X ^ 9
def A2 : (ZMod 1249)[X] := C 401 + C 538 * X + C 839 * X ^ 2 + C 415 * X ^ 3 + C 610 * X ^ 4 + C 23 * X ^ 5 + C 12 * X ^ 6 + C 1020 * X ^ 7 + C 719 * X ^ 8 + C 460 * X ^ 9
def A3 : (ZMod 1249)[X] := C 431 + C 1161 * X + C 526 * X ^ 2 + C 1234 * X ^ 3 + C 140 * X ^ 4 + C 235 * X ^ 5 + C 742 * X ^ 6 + C 1025 * X ^ 7 + C 290 * X ^ 8 + C 79 * X ^ 9
def A4 : (ZMod 1249)[X] := C 352 + C 513 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
def Aastep0 : (ZMod 1249)[X] := C 292 + C 107 * X + C 397 * X ^ 2 + C 634 * X ^ 3 + C 925 * X ^ 4 + C 322 * X ^ 5 + C 524 * X ^ 6 + C 1173 * X ^ 7 + C 157 * X ^ 8 + C 457 * X ^ 9
def Bastep0 : (ZMod 1249)[X] := C 919 + C 135 * X + C 1060 * X ^ 2 + C 1133 * X ^ 3 + C 461 * X ^ 4 + C 837 * X ^ 5 + C 819 * X ^ 6 + C 85 * X ^ 7 + C 396 * X ^ 8 + C 1123 * X ^ 9
def Qastep0 : (ZMod 1249)[X] := C 595 + C 111 * X + C 1198 * X ^ 2 + C 121 * X ^ 3 + C 5 * X ^ 4 + C 1225 * X ^ 5 + C 483 * X ^ 6 + C 587 * X ^ 7 + C 1121 * X ^ 8
def Nastep0 : (ZMod 1249)[X] := C 686 + C 832 * X + C 55 * X ^ 2 + C 574 * X ^ 3 + C 937 * X ^ 4 + C 980 * X ^ 5 + C 438 * X ^ 6 + C 1082 * X ^ 7 + C 51 * X ^ 8 + C 600 * X ^ 9
theorem astep0 : Aastep0 * Bastep0 = S2550F10 * Qastep0 + Nastep0 := by
  have hA : Aastep0.natDegree ≤ 9 := by unfold Aastep0; compute_degree!
  have hB : Bastep0.natDegree ≤ 9 := by unfold Bastep0; compute_degree!
  have hQ : Qastep0.natDegree ≤ 8 := by unfold Qastep0; compute_degree!
  have hN : Nastep0.natDegree ≤ 9 := by unfold Nastep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aastep0 * Bastep0).natDegree ≤ 18 := by
    calc (Aastep0 * Bastep0).natDegree ≤ Aastep0.natDegree + Bastep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qastep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep0).natDegree ≤ S2550F10.natDegree + Qastep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qastep0 + Nastep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep0 + Nastep0).natDegree
        ≤ max (S2550F10 * Qastep0).natDegree Nastep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aastep0, Bastep0, Qastep0, Nastep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Aastep1 : (ZMod 1249)[X] := C 686 + C 832 * X + C 55 * X ^ 2 + C 574 * X ^ 3 + C 937 * X ^ 4 + C 980 * X ^ 5 + C 438 * X ^ 6 + C 1082 * X ^ 7 + C 51 * X ^ 8 + C 600 * X ^ 9
def Bastep1 : (ZMod 1249)[X] := C 591 + C 798 * X + C 929 * X ^ 2 + C 833 * X ^ 3 + C 891 * X ^ 4 + C 821 * X ^ 5 + C 193 * X ^ 6 + C 516 * X ^ 7 + C 696 * X ^ 8 + C 552 * X ^ 9
def Qastep1 : (ZMod 1249)[X] := C 343 + C 366 * X + C 107 * X ^ 2 + C 1018 * X ^ 3 + C 1004 * X ^ 4 + C 622 * X ^ 5 + C 930 * X ^ 6 + C 960 * X ^ 7 + C 215 * X ^ 8
def Nastep1 : (ZMod 1249)[X] := C 401 + C 538 * X + C 839 * X ^ 2 + C 415 * X ^ 3 + C 610 * X ^ 4 + C 23 * X ^ 5 + C 12 * X ^ 6 + C 1020 * X ^ 7 + C 719 * X ^ 8 + C 460 * X ^ 9
theorem astep1 : Aastep1 * Bastep1 = S2550F10 * Qastep1 + Nastep1 := by
  have hA : Aastep1.natDegree ≤ 9 := by unfold Aastep1; compute_degree!
  have hB : Bastep1.natDegree ≤ 9 := by unfold Bastep1; compute_degree!
  have hQ : Qastep1.natDegree ≤ 8 := by unfold Qastep1; compute_degree!
  have hN : Nastep1.natDegree ≤ 9 := by unfold Nastep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aastep1 * Bastep1).natDegree ≤ 18 := by
    calc (Aastep1 * Bastep1).natDegree ≤ Aastep1.natDegree + Bastep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qastep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep1).natDegree ≤ S2550F10.natDegree + Qastep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qastep1 + Nastep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep1 + Nastep1).natDegree
        ≤ max (S2550F10 * Qastep1).natDegree Nastep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aastep1, Bastep1, Qastep1, Nastep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Aastep2 : (ZMod 1249)[X] := C 401 + C 538 * X + C 839 * X ^ 2 + C 415 * X ^ 3 + C 610 * X ^ 4 + C 23 * X ^ 5 + C 12 * X ^ 6 + C 1020 * X ^ 7 + C 719 * X ^ 8 + C 460 * X ^ 9
def Bastep2 : (ZMod 1249)[X] := C 133 + C 294 * X + C 958 * X ^ 2 + C 531 * X ^ 3 + C 752 * X ^ 4 + C 967 * X ^ 5 + C 311 * X ^ 6 + C 854 * X ^ 7 + C 236 * X ^ 8 + C 871 * X ^ 9
def Qastep2 : (ZMod 1249)[X] := C 397 + C 674 * X + C 735 * X ^ 2 + C 642 * X ^ 3 + C 330 * X ^ 4 + C 537 * X ^ 5 + C 9 * X ^ 6 + C 100 * X ^ 7 + C 980 * X ^ 8
def Nastep2 : (ZMod 1249)[X] := C 431 + C 1161 * X + C 526 * X ^ 2 + C 1234 * X ^ 3 + C 140 * X ^ 4 + C 235 * X ^ 5 + C 742 * X ^ 6 + C 1025 * X ^ 7 + C 290 * X ^ 8 + C 79 * X ^ 9
theorem astep2 : Aastep2 * Bastep2 = S2550F10 * Qastep2 + Nastep2 := by
  have hA : Aastep2.natDegree ≤ 9 := by unfold Aastep2; compute_degree!
  have hB : Bastep2.natDegree ≤ 9 := by unfold Bastep2; compute_degree!
  have hQ : Qastep2.natDegree ≤ 8 := by unfold Qastep2; compute_degree!
  have hN : Nastep2.natDegree ≤ 9 := by unfold Nastep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aastep2 * Bastep2).natDegree ≤ 18 := by
    calc (Aastep2 * Bastep2).natDegree ≤ Aastep2.natDegree + Bastep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qastep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep2).natDegree ≤ S2550F10.natDegree + Qastep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qastep2 + Nastep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep2 + Nastep2).natDegree
        ≤ max (S2550F10 * Qastep2).natDegree Nastep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aastep2, Bastep2, Qastep2, Nastep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Aastep3 : (ZMod 1249)[X] := C 431 + C 1161 * X + C 526 * X ^ 2 + C 1234 * X ^ 3 + C 140 * X ^ 4 + C 235 * X ^ 5 + C 742 * X ^ 6 + C 1025 * X ^ 7 + C 290 * X ^ 8 + C 79 * X ^ 9
def Bastep3 : (ZMod 1249)[X] := C 871 + C 629 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
def Qastep3 : (ZMod 1249)[X] := C 343 + C 107 * X + C 715 * X ^ 2 + C 1227 * X ^ 3 + C 290 * X ^ 4 + C 208 * X ^ 5 + C 339 * X ^ 6 + C 387 * X ^ 7 + C 1238 * X ^ 8
def Nastep3 : (ZMod 1249)[X] := C 352 + C 513 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
theorem astep3 : Aastep3 * Bastep3 = S2550F10 * Qastep3 + Nastep3 := by
  have hA : Aastep3.natDegree ≤ 9 := by unfold Aastep3; compute_degree!
  have hB : Bastep3.natDegree ≤ 9 := by unfold Bastep3; compute_degree!
  have hQ : Qastep3.natDegree ≤ 8 := by unfold Qastep3; compute_degree!
  have hN : Nastep3.natDegree ≤ 9 := by unfold Nastep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aastep3 * Bastep3).natDegree ≤ 18 := by
    calc (Aastep3 * Bastep3).natDegree ≤ Aastep3.natDegree + Bastep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qastep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep3).natDegree ≤ S2550F10.natDegree + Qastep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qastep3 + Nastep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qastep3 + Nastep3).natDegree
        ≤ max (S2550F10 * Qastep3).natDegree Nastep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aastep3, Bastep3, Qastep3, Nastep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def B0 : (ZMod 1249)[X] := C 352 + C 513 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
def B1 : (ZMod 1249)[X] := C 32 + C 669 * X + C 509 * X ^ 2 + C 380 * X ^ 3 + C 45 * X ^ 4 + C 1226 * X ^ 5 + C 3 * X ^ 6 + C 546 * X ^ 7 + C 1194 * X ^ 8 + C 190 * X ^ 9
def B2 : (ZMod 1249)[X] := C 151 + C 562 * X + C 504 * X ^ 2 + C 618 * X ^ 3 + C 838 * X ^ 4 + C 1226 * X ^ 5 + C 933 * X ^ 6 + C 464 * X ^ 7 + C 442 * X ^ 8 + C 799 * X ^ 9
def B3 : (ZMod 1249)[X] := C 794 + C 238 * X + C 76 * X ^ 2 + C 212 * X ^ 3 + C 506 * X ^ 4 + C 524 * X ^ 5 + C 703 * X ^ 6 + C 984 * X ^ 7 + C 239 * X ^ 8 + C 455 * X ^ 9
def B4 : (ZMod 1249)[X] := C 568 + C 527 * X + C 1053 * X ^ 2 + C 347 * X ^ 3 + C 937 * X ^ 4 + C 314 * X ^ 5 + C 386 * X ^ 6 + C 457 * X ^ 7 + C 149 * X ^ 8 + C 594 * X ^ 9
def B5 : (ZMod 1249)[X] := C 364 + C 743 * X + C 643 * X ^ 2 + C 733 * X ^ 3 + C 770 * X ^ 4 + C 564 * X ^ 5 + C 85 * X ^ 6 + C 785 * X ^ 7 + C 1017 * X ^ 8 + C 523 * X ^ 9
def B6 : (ZMod 1249)[X] := C 1179 + C 590 * X + C 958 * X ^ 2 + C 616 * X ^ 3 + C 785 * X ^ 4 + C 340 * X ^ 5 + C 668 * X ^ 6 + C 821 * X ^ 7 + C 525 * X ^ 8 + C 556 * X ^ 9
def B7 : (ZMod 1249)[X] := C 676 + C 215 * X + C 455 * X ^ 2 + C 724 * X ^ 3 + C 116 * X ^ 4 + C 1068 * X ^ 5 + C 159 * X ^ 6 + C 176 * X ^ 7 + C 858 * X ^ 8 + C 1132 * X ^ 9
def B8 : (ZMod 1249)[X] := C 691 + C 509 * X + C 517 * X ^ 2 + C 810 * X ^ 3 + C 1170 * X ^ 4 + C 151 * X ^ 5 + C 280 * X ^ 6 + C 426 * X ^ 7 + C 133 * X ^ 8 + C 41 * X ^ 9
def B9 : (ZMod 1249)[X] := C 856 + C 1048 * X + C 844 * X ^ 2 + C 1112 * X ^ 3 + C 24 * X ^ 4 + C 1084 * X ^ 5 + C 664 * X ^ 6 + C 104 * X ^ 7 + C 1041 * X ^ 8 + C 41 * X ^ 9
def B10 : (ZMod 1249)[X] := C 794 + C 903 * X + C 1242 * X ^ 2 + C 100 * X ^ 3 + C 526 * X ^ 4 + C 715 * X ^ 5 + C 798 * X ^ 6 + C 237 * X ^ 7 + C 993 * X ^ 8 + C 685 * X ^ 9
def Abstep0 : (ZMod 1249)[X] := C 352 + C 513 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
def Bbstep0 : (ZMod 1249)[X] := C 352 + C 513 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
def Qbstep0 : (ZMod 1249)[X] := C 1230 + C 1245 * X + C 671 * X ^ 2 + C 293 * X ^ 3 + C 914 * X ^ 4 + C 1176 * X ^ 5 + C 105 * X ^ 6 + C 161 * X ^ 7 + C 26 * X ^ 8
def Nbstep0 : (ZMod 1249)[X] := C 32 + C 669 * X + C 509 * X ^ 2 + C 380 * X ^ 3 + C 45 * X ^ 4 + C 1226 * X ^ 5 + C 3 * X ^ 6 + C 546 * X ^ 7 + C 1194 * X ^ 8 + C 190 * X ^ 9
theorem bstep0 : Abstep0 * Bbstep0 = S2550F10 * Qbstep0 + Nbstep0 := by
  have hA : Abstep0.natDegree ≤ 9 := by unfold Abstep0; compute_degree!
  have hB : Bbstep0.natDegree ≤ 9 := by unfold Bbstep0; compute_degree!
  have hQ : Qbstep0.natDegree ≤ 8 := by unfold Qbstep0; compute_degree!
  have hN : Nbstep0.natDegree ≤ 9 := by unfold Nbstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep0 * Bbstep0).natDegree ≤ 18 := by
    calc (Abstep0 * Bbstep0).natDegree ≤ Abstep0.natDegree + Bbstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep0).natDegree ≤ S2550F10.natDegree + Qbstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep0 + Nbstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep0 + Nbstep0).natDegree
        ≤ max (S2550F10 * Qbstep0).natDegree Nbstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep0, Bbstep0, Qbstep0, Nbstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep1 : (ZMod 1249)[X] := C 32 + C 669 * X + C 509 * X ^ 2 + C 380 * X ^ 3 + C 45 * X ^ 4 + C 1226 * X ^ 5 + C 3 * X ^ 6 + C 546 * X ^ 7 + C 1194 * X ^ 8 + C 190 * X ^ 9
def Bbstep1 : (ZMod 1249)[X] := C 32 + C 669 * X + C 509 * X ^ 2 + C 380 * X ^ 3 + C 45 * X ^ 4 + C 1226 * X ^ 5 + C 3 * X ^ 6 + C 546 * X ^ 7 + C 1194 * X ^ 8 + C 190 * X ^ 9
def Qbstep1 : (ZMod 1249)[X] := C 654 + C 1027 * X + C 831 * X ^ 2 + C 1046 * X ^ 3 + C 283 * X ^ 4 + C 335 * X ^ 5 + C 272 * X ^ 6 + C 608 * X ^ 7 + C 1128 * X ^ 8
def Nbstep1 : (ZMod 1249)[X] := C 151 + C 562 * X + C 504 * X ^ 2 + C 618 * X ^ 3 + C 838 * X ^ 4 + C 1226 * X ^ 5 + C 933 * X ^ 6 + C 464 * X ^ 7 + C 442 * X ^ 8 + C 799 * X ^ 9
theorem bstep1 : Abstep1 * Bbstep1 = S2550F10 * Qbstep1 + Nbstep1 := by
  have hA : Abstep1.natDegree ≤ 9 := by unfold Abstep1; compute_degree!
  have hB : Bbstep1.natDegree ≤ 9 := by unfold Bbstep1; compute_degree!
  have hQ : Qbstep1.natDegree ≤ 8 := by unfold Qbstep1; compute_degree!
  have hN : Nbstep1.natDegree ≤ 9 := by unfold Nbstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep1 * Bbstep1).natDegree ≤ 18 := by
    calc (Abstep1 * Bbstep1).natDegree ≤ Abstep1.natDegree + Bbstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep1).natDegree ≤ S2550F10.natDegree + Qbstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep1 + Nbstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep1 + Nbstep1).natDegree
        ≤ max (S2550F10 * Qbstep1).natDegree Nbstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep1, Bbstep1, Qbstep1, Nbstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep2 : (ZMod 1249)[X] := C 151 + C 562 * X + C 504 * X ^ 2 + C 618 * X ^ 3 + C 838 * X ^ 4 + C 1226 * X ^ 5 + C 933 * X ^ 6 + C 464 * X ^ 7 + C 442 * X ^ 8 + C 799 * X ^ 9
def Bbstep2 : (ZMod 1249)[X] := C 151 + C 562 * X + C 504 * X ^ 2 + C 618 * X ^ 3 + C 838 * X ^ 4 + C 1226 * X ^ 5 + C 933 * X ^ 6 + C 464 * X ^ 7 + C 442 * X ^ 8 + C 799 * X ^ 9
def Qbstep2 : (ZMod 1249)[X] := C 979 + C 124 * X + C 1103 * X ^ 2 + C 1080 * X ^ 3 + C 1008 * X ^ 4 + C 781 * X ^ 5 + C 1108 * X ^ 6 + C 717 * X ^ 7 + C 162 * X ^ 8
def Nbstep2 : (ZMod 1249)[X] := C 794 + C 238 * X + C 76 * X ^ 2 + C 212 * X ^ 3 + C 506 * X ^ 4 + C 524 * X ^ 5 + C 703 * X ^ 6 + C 984 * X ^ 7 + C 239 * X ^ 8 + C 455 * X ^ 9
theorem bstep2 : Abstep2 * Bbstep2 = S2550F10 * Qbstep2 + Nbstep2 := by
  have hA : Abstep2.natDegree ≤ 9 := by unfold Abstep2; compute_degree!
  have hB : Bbstep2.natDegree ≤ 9 := by unfold Bbstep2; compute_degree!
  have hQ : Qbstep2.natDegree ≤ 8 := by unfold Qbstep2; compute_degree!
  have hN : Nbstep2.natDegree ≤ 9 := by unfold Nbstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep2 * Bbstep2).natDegree ≤ 18 := by
    calc (Abstep2 * Bbstep2).natDegree ≤ Abstep2.natDegree + Bbstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep2).natDegree ≤ S2550F10.natDegree + Qbstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep2 + Nbstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep2 + Nbstep2).natDegree
        ≤ max (S2550F10 * Qbstep2).natDegree Nbstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep2, Bbstep2, Qbstep2, Nbstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep3 : (ZMod 1249)[X] := C 794 + C 238 * X + C 76 * X ^ 2 + C 212 * X ^ 3 + C 506 * X ^ 4 + C 524 * X ^ 5 + C 703 * X ^ 6 + C 984 * X ^ 7 + C 239 * X ^ 8 + C 455 * X ^ 9
def Bbstep3 : (ZMod 1249)[X] := C 794 + C 238 * X + C 76 * X ^ 2 + C 212 * X ^ 3 + C 506 * X ^ 4 + C 524 * X ^ 5 + C 703 * X ^ 6 + C 984 * X ^ 7 + C 239 * X ^ 8 + C 455 * X ^ 9
def Qbstep3 : (ZMod 1249)[X] := C 974 + C 120 * X + C 476 * X ^ 2 + C 202 * X ^ 3 + C 1160 * X ^ 4 + C 880 * X ^ 5 + C 444 * X ^ 6 + C 185 * X ^ 7 + C 940 * X ^ 8
def Nbstep3 : (ZMod 1249)[X] := C 568 + C 527 * X + C 1053 * X ^ 2 + C 347 * X ^ 3 + C 937 * X ^ 4 + C 314 * X ^ 5 + C 386 * X ^ 6 + C 457 * X ^ 7 + C 149 * X ^ 8 + C 594 * X ^ 9
theorem bstep3 : Abstep3 * Bbstep3 = S2550F10 * Qbstep3 + Nbstep3 := by
  have hA : Abstep3.natDegree ≤ 9 := by unfold Abstep3; compute_degree!
  have hB : Bbstep3.natDegree ≤ 9 := by unfold Bbstep3; compute_degree!
  have hQ : Qbstep3.natDegree ≤ 8 := by unfold Qbstep3; compute_degree!
  have hN : Nbstep3.natDegree ≤ 9 := by unfold Nbstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep3 * Bbstep3).natDegree ≤ 18 := by
    calc (Abstep3 * Bbstep3).natDegree ≤ Abstep3.natDegree + Bbstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep3).natDegree ≤ S2550F10.natDegree + Qbstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep3 + Nbstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep3 + Nbstep3).natDegree
        ≤ max (S2550F10 * Qbstep3).natDegree Nbstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep3, Bbstep3, Qbstep3, Nbstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep4 : (ZMod 1249)[X] := C 568 + C 527 * X + C 1053 * X ^ 2 + C 347 * X ^ 3 + C 937 * X ^ 4 + C 314 * X ^ 5 + C 386 * X ^ 6 + C 457 * X ^ 7 + C 149 * X ^ 8 + C 594 * X ^ 9
def Bbstep4 : (ZMod 1249)[X] := C 568 + C 527 * X + C 1053 * X ^ 2 + C 347 * X ^ 3 + C 937 * X ^ 4 + C 314 * X ^ 5 + C 386 * X ^ 6 + C 457 * X ^ 7 + C 149 * X ^ 8 + C 594 * X ^ 9
def Qbstep4 : (ZMod 1249)[X] := C 168 + C 59 * X + C 415 * X ^ 2 + C 852 * X ^ 3 + C 712 * X ^ 4 + C 1184 * X ^ 5 + C 346 * X ^ 6 + C 861 * X ^ 7 + C 618 * X ^ 8
def Nbstep4 : (ZMod 1249)[X] := C 364 + C 743 * X + C 643 * X ^ 2 + C 733 * X ^ 3 + C 770 * X ^ 4 + C 564 * X ^ 5 + C 85 * X ^ 6 + C 785 * X ^ 7 + C 1017 * X ^ 8 + C 523 * X ^ 9
theorem bstep4 : Abstep4 * Bbstep4 = S2550F10 * Qbstep4 + Nbstep4 := by
  have hA : Abstep4.natDegree ≤ 9 := by unfold Abstep4; compute_degree!
  have hB : Bbstep4.natDegree ≤ 9 := by unfold Bbstep4; compute_degree!
  have hQ : Qbstep4.natDegree ≤ 8 := by unfold Qbstep4; compute_degree!
  have hN : Nbstep4.natDegree ≤ 9 := by unfold Nbstep4; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep4 * Bbstep4).natDegree ≤ 18 := by
    calc (Abstep4 * Bbstep4).natDegree ≤ Abstep4.natDegree + Bbstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep4).natDegree ≤ S2550F10.natDegree + Qbstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep4 + Nbstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep4 + Nbstep4).natDegree
        ≤ max (S2550F10 * Qbstep4).natDegree Nbstep4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep4, Bbstep4, Qbstep4, Nbstep4, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep5 : (ZMod 1249)[X] := C 364 + C 743 * X + C 643 * X ^ 2 + C 733 * X ^ 3 + C 770 * X ^ 4 + C 564 * X ^ 5 + C 85 * X ^ 6 + C 785 * X ^ 7 + C 1017 * X ^ 8 + C 523 * X ^ 9
def Bbstep5 : (ZMod 1249)[X] := C 364 + C 743 * X + C 643 * X ^ 2 + C 733 * X ^ 3 + C 770 * X ^ 4 + C 564 * X ^ 5 + C 85 * X ^ 6 + C 785 * X ^ 7 + C 1017 * X ^ 8 + C 523 * X ^ 9
def Qbstep5 : (ZMod 1249)[X] := C 1189 + C 419 * X + C 925 * X ^ 2 + C 487 * X ^ 3 + C 345 * X ^ 4 + C 908 * X ^ 5 + C 736 * X ^ 6 + C 774 * X ^ 7 + C 1247 * X ^ 8
def Nbstep5 : (ZMod 1249)[X] := C 1179 + C 590 * X + C 958 * X ^ 2 + C 616 * X ^ 3 + C 785 * X ^ 4 + C 340 * X ^ 5 + C 668 * X ^ 6 + C 821 * X ^ 7 + C 525 * X ^ 8 + C 556 * X ^ 9
theorem bstep5 : Abstep5 * Bbstep5 = S2550F10 * Qbstep5 + Nbstep5 := by
  have hA : Abstep5.natDegree ≤ 9 := by unfold Abstep5; compute_degree!
  have hB : Bbstep5.natDegree ≤ 9 := by unfold Bbstep5; compute_degree!
  have hQ : Qbstep5.natDegree ≤ 8 := by unfold Qbstep5; compute_degree!
  have hN : Nbstep5.natDegree ≤ 9 := by unfold Nbstep5; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep5 * Bbstep5).natDegree ≤ 18 := by
    calc (Abstep5 * Bbstep5).natDegree ≤ Abstep5.natDegree + Bbstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep5).natDegree ≤ S2550F10.natDegree + Qbstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep5 + Nbstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep5 + Nbstep5).natDegree
        ≤ max (S2550F10 * Qbstep5).natDegree Nbstep5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep5, Bbstep5, Qbstep5, Nbstep5, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep6 : (ZMod 1249)[X] := C 1179 + C 590 * X + C 958 * X ^ 2 + C 616 * X ^ 3 + C 785 * X ^ 4 + C 340 * X ^ 5 + C 668 * X ^ 6 + C 821 * X ^ 7 + C 525 * X ^ 8 + C 556 * X ^ 9
def Bbstep6 : (ZMod 1249)[X] := C 1179 + C 590 * X + C 958 * X ^ 2 + C 616 * X ^ 3 + C 785 * X ^ 4 + C 340 * X ^ 5 + C 668 * X ^ 6 + C 821 * X ^ 7 + C 525 * X ^ 8 + C 556 * X ^ 9
def Qbstep6 : (ZMod 1249)[X] := C 705 + C 786 * X + C 649 * X ^ 2 + C 731 * X ^ 3 + C 422 * X ^ 4 + C 630 * X ^ 5 + C 888 * X ^ 6 + C 668 * X ^ 7 + C 633 * X ^ 8
def Nbstep6 : (ZMod 1249)[X] := C 676 + C 215 * X + C 455 * X ^ 2 + C 724 * X ^ 3 + C 116 * X ^ 4 + C 1068 * X ^ 5 + C 159 * X ^ 6 + C 176 * X ^ 7 + C 858 * X ^ 8 + C 1132 * X ^ 9
theorem bstep6 : Abstep6 * Bbstep6 = S2550F10 * Qbstep6 + Nbstep6 := by
  have hA : Abstep6.natDegree ≤ 9 := by unfold Abstep6; compute_degree!
  have hB : Bbstep6.natDegree ≤ 9 := by unfold Bbstep6; compute_degree!
  have hQ : Qbstep6.natDegree ≤ 8 := by unfold Qbstep6; compute_degree!
  have hN : Nbstep6.natDegree ≤ 9 := by unfold Nbstep6; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep6 * Bbstep6).natDegree ≤ 18 := by
    calc (Abstep6 * Bbstep6).natDegree ≤ Abstep6.natDegree + Bbstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep6).natDegree ≤ S2550F10.natDegree + Qbstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep6 + Nbstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep6 + Nbstep6).natDegree
        ≤ max (S2550F10 * Qbstep6).natDegree Nbstep6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep6, Bbstep6, Qbstep6, Nbstep6, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep7 : (ZMod 1249)[X] := C 676 + C 215 * X + C 455 * X ^ 2 + C 724 * X ^ 3 + C 116 * X ^ 4 + C 1068 * X ^ 5 + C 159 * X ^ 6 + C 176 * X ^ 7 + C 858 * X ^ 8 + C 1132 * X ^ 9
def Bbstep7 : (ZMod 1249)[X] := C 676 + C 215 * X + C 455 * X ^ 2 + C 724 * X ^ 3 + C 116 * X ^ 4 + C 1068 * X ^ 5 + C 159 * X ^ 6 + C 176 * X ^ 7 + C 858 * X ^ 8 + C 1132 * X ^ 9
def Qbstep7 : (ZMod 1249)[X] := C 819 + C 927 * X + C 795 * X ^ 2 + C 709 * X ^ 3 + C 952 * X ^ 4 + C 171 * X ^ 5 + C 78 * X ^ 6 + C 90 * X ^ 7 + C 1199 * X ^ 8
def Nbstep7 : (ZMod 1249)[X] := C 691 + C 509 * X + C 517 * X ^ 2 + C 810 * X ^ 3 + C 1170 * X ^ 4 + C 151 * X ^ 5 + C 280 * X ^ 6 + C 426 * X ^ 7 + C 133 * X ^ 8 + C 41 * X ^ 9
theorem bstep7 : Abstep7 * Bbstep7 = S2550F10 * Qbstep7 + Nbstep7 := by
  have hA : Abstep7.natDegree ≤ 9 := by unfold Abstep7; compute_degree!
  have hB : Bbstep7.natDegree ≤ 9 := by unfold Bbstep7; compute_degree!
  have hQ : Qbstep7.natDegree ≤ 8 := by unfold Qbstep7; compute_degree!
  have hN : Nbstep7.natDegree ≤ 9 := by unfold Nbstep7; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep7 * Bbstep7).natDegree ≤ 18 := by
    calc (Abstep7 * Bbstep7).natDegree ≤ Abstep7.natDegree + Bbstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep7).natDegree ≤ S2550F10.natDegree + Qbstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep7 + Nbstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep7 + Nbstep7).natDegree
        ≤ max (S2550F10 * Qbstep7).natDegree Nbstep7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep7, Bbstep7, Qbstep7, Nbstep7, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep8 : (ZMod 1249)[X] := C 691 + C 509 * X + C 517 * X ^ 2 + C 810 * X ^ 3 + C 1170 * X ^ 4 + C 151 * X ^ 5 + C 280 * X ^ 6 + C 426 * X ^ 7 + C 133 * X ^ 8 + C 41 * X ^ 9
def Bbstep8 : (ZMod 1249)[X] := C 691 + C 509 * X + C 517 * X ^ 2 + C 810 * X ^ 3 + C 1170 * X ^ 4 + C 151 * X ^ 5 + C 280 * X ^ 6 + C 426 * X ^ 7 + C 133 * X ^ 8 + C 41 * X ^ 9
def Qbstep8 : (ZMod 1249)[X] := C 811 + C 40 * X + C 1024 * X ^ 2 + C 715 * X ^ 3 + C 584 * X ^ 4 + C 542 * X ^ 5 + C 964 * X ^ 6 + C 727 * X ^ 7 + C 432 * X ^ 8
def Nbstep8 : (ZMod 1249)[X] := C 856 + C 1048 * X + C 844 * X ^ 2 + C 1112 * X ^ 3 + C 24 * X ^ 4 + C 1084 * X ^ 5 + C 664 * X ^ 6 + C 104 * X ^ 7 + C 1041 * X ^ 8 + C 41 * X ^ 9
theorem bstep8 : Abstep8 * Bbstep8 = S2550F10 * Qbstep8 + Nbstep8 := by
  have hA : Abstep8.natDegree ≤ 9 := by unfold Abstep8; compute_degree!
  have hB : Bbstep8.natDegree ≤ 9 := by unfold Bbstep8; compute_degree!
  have hQ : Qbstep8.natDegree ≤ 8 := by unfold Qbstep8; compute_degree!
  have hN : Nbstep8.natDegree ≤ 9 := by unfold Nbstep8; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep8 * Bbstep8).natDegree ≤ 18 := by
    calc (Abstep8 * Bbstep8).natDegree ≤ Abstep8.natDegree + Bbstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep8).natDegree ≤ S2550F10.natDegree + Qbstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep8 + Nbstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep8 + Nbstep8).natDegree
        ≤ max (S2550F10 * Qbstep8).natDegree Nbstep8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep8, Bbstep8, Qbstep8, Nbstep8, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Abstep9 : (ZMod 1249)[X] := C 856 + C 1048 * X + C 844 * X ^ 2 + C 1112 * X ^ 3 + C 24 * X ^ 4 + C 1084 * X ^ 5 + C 664 * X ^ 6 + C 104 * X ^ 7 + C 1041 * X ^ 8 + C 41 * X ^ 9
def Bbstep9 : (ZMod 1249)[X] := C 856 + C 1048 * X + C 844 * X ^ 2 + C 1112 * X ^ 3 + C 24 * X ^ 4 + C 1084 * X ^ 5 + C 664 * X ^ 6 + C 104 * X ^ 7 + C 1041 * X ^ 8 + C 41 * X ^ 9
def Qbstep9 : (ZMod 1249)[X] := C 1094 + C 537 * X + C 91 * X ^ 2 + C 21 * X ^ 3 + C 1189 * X ^ 4 + C 251 * X ^ 5 + C 1235 * X ^ 6 + C 243 * X ^ 7 + C 432 * X ^ 8
def Nbstep9 : (ZMod 1249)[X] := C 794 + C 903 * X + C 1242 * X ^ 2 + C 100 * X ^ 3 + C 526 * X ^ 4 + C 715 * X ^ 5 + C 798 * X ^ 6 + C 237 * X ^ 7 + C 993 * X ^ 8 + C 685 * X ^ 9
theorem bstep9 : Abstep9 * Bbstep9 = S2550F10 * Qbstep9 + Nbstep9 := by
  have hA : Abstep9.natDegree ≤ 9 := by unfold Abstep9; compute_degree!
  have hB : Bbstep9.natDegree ≤ 9 := by unfold Bbstep9; compute_degree!
  have hQ : Qbstep9.natDegree ≤ 8 := by unfold Qbstep9; compute_degree!
  have hN : Nbstep9.natDegree ≤ 9 := by unfold Nbstep9; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Abstep9 * Bbstep9).natDegree ≤ 18 := by
    calc (Abstep9 * Bbstep9).natDegree ≤ Abstep9.natDegree + Bbstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qbstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep9).natDegree ≤ S2550F10.natDegree + Qbstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qbstep9 + Nbstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qbstep9 + Nbstep9).natDegree
        ≤ max (S2550F10 * Qbstep9).natDegree Nbstep9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Abstep9, Bbstep9, Qbstep9, Nbstep9, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

end