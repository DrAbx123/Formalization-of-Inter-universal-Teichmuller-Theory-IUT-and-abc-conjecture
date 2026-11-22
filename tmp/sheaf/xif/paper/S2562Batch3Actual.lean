import tmp.sheaf.xif.paper.S2561Batch2Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2561Batch2Actual

namespace LeanFormal.IUT.XiFPaper.S2562Batch3Actual

def V0 : (ZMod 1249)[X] := 644 + X * 889 + X ^ 2 * 20 + X ^ 3 * 552 + X ^ 4 * 1015 + X ^ 5 * 1199 + X ^ 6 * 1208 + X ^ 7 * 524 + X ^ 8 * 407 + X ^ 9 * 264
def V1 : (ZMod 1249)[X] := 836 + X * 723 + X ^ 2 * 352 + X ^ 3 * 587 + X ^ 4 * 708 + X ^ 5 * 162 + X ^ 6 * 71 + X ^ 7 * 1235 + X ^ 8 * 651 + X ^ 9 * 1108
def V2 : (ZMod 1249)[X] := 1234 + X * 815 + X ^ 2 * 357 + X ^ 3 * 942 + X ^ 4 * 855 + X ^ 5 * 726 + X ^ 6 * 636 + X ^ 7 * 201 + X ^ 8 * 656 + X ^ 9 * 619
def V3 : (ZMod 1249)[X] := 41 + X * 1137 + X ^ 2 * 574 + X ^ 3 * 191 + X ^ 4 * 781 + X ^ 5 * 702 + X ^ 6 * 347 + X ^ 7 * 706 + X ^ 8 * 604 + X ^ 9 * 135
def V4 : (ZMod 1249)[X] := 871 + X * 629 + X ^ 2 * 1077 + X ^ 3 * 1032 + X ^ 4 * 142 + X ^ 5 * 643 + X ^ 6 * 946 + X ^ 7 * 1025 + X ^ 8 * 796 + X ^ 9 * 1154
def Lvstep0 : (ZMod 1249)[X] := 892 + X * 1128 + X ^ 2 * 1164 + X ^ 3 * 1130 + X ^ 4 * 8 + X ^ 5 * 673 + X ^ 6 * 1233 + X ^ 7 * 568 + X ^ 8 * 1200 + X ^ 9 * 781 + X ^ 10 * 524 + X ^ 11 * 239 + X ^ 12 * 663 + X ^ 13 * 478 + X ^ 14 * 851 + X ^ 15 * 58 + X ^ 16 * 1089 + X ^ 17 * 1160 + X ^ 18 * 807
def Mvstep0 : (ZMod 1249)[X] := 892 + X * 1128 + X ^ 2 * 1164 + X ^ 3 * 1130 + X ^ 4 * 8 + X ^ 5 * 673 + X ^ 6 * 1233 + X ^ 7 * 568 + X ^ 8 * 1200 + X ^ 9 * 781 + X ^ 10 * 524 + X ^ 11 * 239 + X ^ 12 * 663 + X ^ 13 * 478 + X ^ 14 * 851 + X ^ 15 * 58 + X ^ 16 * 1089 + X ^ 17 * 1160 + X ^ 18 * 807
theorem vstep0 : Lvstep0 = Mvstep0 := by
  have hL : Lvstep0.natDegree ≤ 18 := by unfold Lvstep0; compute_degree!
  have hR : Mvstep0.natDegree ≤ 18 := by unfold Mvstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lvstep0, Mvstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lvstep1 : (ZMod 1249)[X] := 163 + X * 659 + X ^ 2 * 420 + X ^ 3 * 5 + X ^ 4 * 1190 + X ^ 5 * 988 + X ^ 6 * 185 + X ^ 7 * 1065 + X ^ 8 * 893 + X ^ 10 * 107 + X ^ 11 * 129 + X ^ 12 * 153 + X ^ 13 * 1098 + X ^ 14 * 93 + X ^ 15 * 900 + X ^ 16 * 163 + X ^ 17 * 241 + X ^ 18 * 873
def Mvstep1 : (ZMod 1249)[X] := 163 + X * 659 + X ^ 2 * 420 + X ^ 3 * 5 + X ^ 4 * 1190 + X ^ 5 * 988 + X ^ 6 * 185 + X ^ 7 * 1065 + X ^ 8 * 893 + X ^ 10 * 107 + X ^ 11 * 129 + X ^ 12 * 153 + X ^ 13 * 1098 + X ^ 14 * 93 + X ^ 15 * 900 + X ^ 16 * 163 + X ^ 17 * 241 + X ^ 18 * 873
theorem vstep1 : Lvstep1 = Mvstep1 := by
  have hL : Lvstep1.natDegree ≤ 18 := by unfold Lvstep1; compute_degree!
  have hR : Mvstep1.natDegree ≤ 18 := by unfold Mvstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lvstep1, Mvstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lvstep2 : (ZMod 1249)[X] := 146 + X * 1028 + X ^ 2 * 981 + X ^ 3 * 131 + X ^ 4 * 1215 + X ^ 5 * 706 + X ^ 6 * 550 + X ^ 7 * 618 + X ^ 8 * 630 + X ^ 9 * 1192 + X ^ 10 * 106 + X ^ 11 * 105 + X ^ 12 * 1206 + X ^ 13 * 803 + X ^ 14 * 709 + X ^ 15 * 1089 + X ^ 16 * 160 + X ^ 17 * 907 + X ^ 18 * 38
def Mvstep2 : (ZMod 1249)[X] := 146 + X * 1028 + X ^ 2 * 981 + X ^ 3 * 131 + X ^ 4 * 1215 + X ^ 5 * 706 + X ^ 6 * 550 + X ^ 7 * 618 + X ^ 8 * 630 + X ^ 9 * 1192 + X ^ 10 * 106 + X ^ 11 * 105 + X ^ 12 * 1206 + X ^ 13 * 803 + X ^ 14 * 709 + X ^ 15 * 1089 + X ^ 16 * 160 + X ^ 17 * 907 + X ^ 18 * 38
theorem vstep2 : Lvstep2 = Mvstep2 := by
  have hL : Lvstep2.natDegree ≤ 18 := by unfold Lvstep2; compute_degree!
  have hR : Mvstep2.natDegree ≤ 18 := by unfold Mvstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lvstep2, Mvstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lvstep3 : (ZMod 1249)[X] := 792 + X * 391 + X ^ 2 * 16 + X ^ 3 * 875 + X ^ 4 * 899 + X ^ 5 * 87 + X ^ 6 * 457 + X ^ 7 * 34 + X ^ 8 * 835 + X ^ 9 * 45 + X ^ 10 * 682 + X ^ 11 * 577 + X ^ 12 * 600 + X ^ 13 * 940 + X ^ 14 * 194 + X ^ 15 * 334 + X ^ 16 * 289 + X ^ 17 * 1115 + X ^ 18 * 66
def Mvstep3 : (ZMod 1249)[X] := 792 + X * 391 + X ^ 2 * 16 + X ^ 3 * 875 + X ^ 4 * 899 + X ^ 5 * 87 + X ^ 6 * 457 + X ^ 7 * 34 + X ^ 8 * 835 + X ^ 9 * 45 + X ^ 10 * 682 + X ^ 11 * 577 + X ^ 12 * 600 + X ^ 13 * 940 + X ^ 14 * 194 + X ^ 15 * 334 + X ^ 16 * 289 + X ^ 17 * 1115 + X ^ 18 * 66
theorem vstep3 : Lvstep3 = Mvstep3 := by
  have hL : Lvstep3.natDegree ≤ 18 := by unfold Lvstep3; compute_degree!
  have hR : Mvstep3.natDegree ≤ 18 := by unfold Mvstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lvstep3, Mvstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def W0 : (ZMod 1249)[X] := 871 + X * 629 + X ^ 2 * 1077 + X ^ 3 * 1032 + X ^ 4 * 142 + X ^ 5 * 643 + X ^ 6 * 946 + X ^ 7 * 1025 + X ^ 8 * 796 + X ^ 9 * 1154
def W1 : (ZMod 1249)[X] := 772 + X * 188 + X ^ 2 * 1208 + X ^ 3 * 1035 + X ^ 4 * 218 + X ^ 5 * 650 + X ^ 6 * 837 + X ^ 7 * 285 + X ^ 8 * 709 + X ^ 9 * 1130
def W2 : (ZMod 1249)[X] := 114 + X * 215 + X ^ 2 * 1065 + X ^ 3 * 1006 + X ^ 4 * 403 + X ^ 5 * 264 + X ^ 6 * 603 + X ^ 7 * 927 + X ^ 8 * 1062 + X ^ 9 * 797
def W3 : (ZMod 1249)[X] := 725 + X * 641 + X ^ 2 * 684 + X ^ 3 * 263 + X ^ 4 * 920 + X ^ 5 * 163 + X ^ 6 * 70 + X ^ 7 * 810 + X ^ 8 * 193 + X ^ 9 * 840
def W4 : (ZMod 1249)[X] := 1139 + X * 794 + X ^ 2 * 1095 + X ^ 3 * 682 + X ^ 4 * 28 + X ^ 5 * 566 + X ^ 6 * 788 + X ^ 7 * 715 + X ^ 8 * 1007 + X ^ 9 * 187
def W5 : (ZMod 1249)[X] := 133 + X * 294 + X ^ 2 * 958 + X ^ 3 * 531 + X ^ 4 * 752 + X ^ 5 * 967 + X ^ 6 * 311 + X ^ 7 * 854 + X ^ 8 * 236 + X ^ 9 * 871
def W6 : (ZMod 1249)[X] := 591 + X * 798 + X ^ 2 * 929 + X ^ 3 * 833 + X ^ 4 * 891 + X ^ 5 * 821 + X ^ 6 * 193 + X ^ 7 * 516 + X ^ 8 * 696 + X ^ 9 * 552
def W7 : (ZMod 1249)[X] := 919 + X * 135 + X ^ 2 * 1060 + X ^ 3 * 1133 + X ^ 4 * 461 + X ^ 5 * 837 + X ^ 6 * 819 + X ^ 7 * 85 + X ^ 8 * 396 + X ^ 9 * 1123
def W8 : (ZMod 1249)[X] := 204 + X * 1154 + X ^ 2 * 425 + X ^ 3 * 529 + X ^ 4 * 850 + X ^ 5 * 810 + X ^ 6 * 934 + X ^ 7 * 1154 + X ^ 8 * 549 + X ^ 9 * 137
def W9 : (ZMod 1249)[X] := 1193 + X * 614 + X ^ 2 * 905 + X ^ 3 * 441 + X ^ 4 * 427 + X ^ 5 * 798 + X ^ 6 * 805 + X ^ 7 * 801 + X ^ 8 * 1187 + X ^ 9 * 627
def W10 : (ZMod 1249)[X] := 292 + X * 107 + X ^ 2 * 397 + X ^ 3 * 634 + X ^ 4 * 925 + X ^ 5 * 322 + X ^ 6 * 524 + X ^ 7 * 1173 + X ^ 8 * 157 + X ^ 9 * 457
def Lwstep0 : (ZMod 1249)[X] := 498 + X * 345 + X ^ 2 * 1093 + X ^ 3 * 134 + X ^ 4 * 215 + X ^ 5 * 739 + X ^ 6 * 782 + X ^ 7 * 1203 + X ^ 8 * 934 + X ^ 9 * 530 + X ^ 10 * 54 + X ^ 11 * 828 + X ^ 12 * 1095 + X ^ 13 * 826 + X ^ 14 * 186 + X ^ 15 * 722 + X ^ 16 * 467 + X ^ 17 * 1138 + X ^ 18 * 282
def Mwstep0 : (ZMod 1249)[X] := 498 + X * 345 + X ^ 2 * 1093 + X ^ 3 * 134 + X ^ 4 * 215 + X ^ 5 * 739 + X ^ 6 * 782 + X ^ 7 * 1203 + X ^ 8 * 934 + X ^ 9 * 530 + X ^ 10 * 54 + X ^ 11 * 828 + X ^ 12 * 1095 + X ^ 13 * 826 + X ^ 14 * 186 + X ^ 15 * 722 + X ^ 16 * 467 + X ^ 17 * 1138 + X ^ 18 * 282
theorem wstep0 : Lwstep0 = Mwstep0 := by
  have hL : Lwstep0.natDegree ≤ 18 := by unfold Lwstep0; compute_degree!
  have hR : Mwstep0.natDegree ≤ 18 := by unfold Mwstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep0, Mwstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep1 : (ZMod 1249)[X] := 211 + X * 504 + X ^ 2 * 767 + X ^ 3 * 141 + X ^ 4 * 515 + X ^ 5 * 249 + X ^ 6 * 900 + X ^ 7 * 1134 + X ^ 8 * 768 + X ^ 9 * 879 + X ^ 10 * 520 + X ^ 11 * 651 + X ^ 12 * 1020 + X ^ 13 * 484 + X ^ 14 * 532 + X ^ 15 * 88 + X ^ 16 * 199 + X ^ 17 * 1122 + X ^ 18 * 422
def Mwstep1 : (ZMod 1249)[X] := 211 + X * 504 + X ^ 2 * 767 + X ^ 3 * 141 + X ^ 4 * 515 + X ^ 5 * 249 + X ^ 6 * 900 + X ^ 7 * 1134 + X ^ 8 * 768 + X ^ 9 * 879 + X ^ 10 * 520 + X ^ 11 * 651 + X ^ 12 * 1020 + X ^ 13 * 484 + X ^ 14 * 532 + X ^ 15 * 88 + X ^ 16 * 199 + X ^ 17 * 1122 + X ^ 18 * 422
theorem wstep1 : Lwstep1 = Mwstep1 := by
  have hL : Lwstep1.natDegree ≤ 18 := by unfold Lwstep1; compute_degree!
  have hR : Mwstep1.natDegree ≤ 18 := by unfold Mwstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep1, Mwstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep2 : (ZMod 1249)[X] := 506 + X * 309 + X ^ 2 * 526 + X ^ 3 * 368 + X ^ 4 * 17 + X ^ 5 * 664 + X ^ 6 * 628 + X ^ 7 * 278 + X ^ 8 * 809 + X ^ 9 * 889 + X ^ 10 * 881 + X ^ 11 * 73 + X ^ 12 * 253 + X ^ 13 * 438 + X ^ 14 * 467 + X ^ 15 * 1225 + X ^ 16 * 68 + X ^ 17 * 433 + X ^ 18 * 717
def Mwstep2 : (ZMod 1249)[X] := 506 + X * 309 + X ^ 2 * 526 + X ^ 3 * 368 + X ^ 4 * 17 + X ^ 5 * 664 + X ^ 6 * 628 + X ^ 7 * 278 + X ^ 8 * 809 + X ^ 9 * 889 + X ^ 10 * 881 + X ^ 11 * 73 + X ^ 12 * 253 + X ^ 13 * 438 + X ^ 14 * 467 + X ^ 15 * 1225 + X ^ 16 * 68 + X ^ 17 * 433 + X ^ 18 * 717
theorem wstep2 : Lwstep2 = Mwstep2 := by
  have hL : Lwstep2.natDegree ≤ 18 := by unfold Lwstep2; compute_degree!
  have hR : Mwstep2.natDegree ≤ 18 := by unfold Mwstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep2, Mwstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep3 : (ZMod 1249)[X] := 1045 + X * 194 + X ^ 2 * 54 + X ^ 3 * 495 + X ^ 4 * 734 + X ^ 5 * 745 + X ^ 6 * 756 + X ^ 7 * 222 + X ^ 8 * 546 + X ^ 9 * 76 + X ^ 10 * 122 + X ^ 11 * 1070 + X ^ 12 * 523 + X ^ 13 * 796 + X ^ 14 * 226 + X ^ 15 * 604 + X ^ 16 * 418 + X ^ 17 * 749 + X ^ 18 * 1164
def Mwstep3 : (ZMod 1249)[X] := 1045 + X * 194 + X ^ 2 * 54 + X ^ 3 * 495 + X ^ 4 * 734 + X ^ 5 * 745 + X ^ 6 * 756 + X ^ 7 * 222 + X ^ 8 * 546 + X ^ 9 * 76 + X ^ 10 * 122 + X ^ 11 * 1070 + X ^ 12 * 523 + X ^ 13 * 796 + X ^ 14 * 226 + X ^ 15 * 604 + X ^ 16 * 418 + X ^ 17 * 749 + X ^ 18 * 1164
theorem wstep3 : Lwstep3 = Mwstep3 := by
  have hL : Lwstep3.natDegree ≤ 18 := by unfold Lwstep3; compute_degree!
  have hR : Mwstep3.natDegree ≤ 18 := by unfold Mwstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep3, Mwstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep4 : (ZMod 1249)[X] := 859 + X * 180 + X ^ 2 * 1097 + X ^ 3 * 92 + X ^ 4 * 203 + X ^ 5 * 905 + X ^ 6 * 394 + X ^ 7 * 1174 + X ^ 8 * 140 + X ^ 9 * 1240 + X ^ 10 * 106 + X ^ 11 * 1057 + X ^ 12 * 678 + X ^ 13 * 309 + X ^ 14 * 540 + X ^ 15 * 1110 + X ^ 16 * 1234 + X ^ 17 * 669 + X ^ 18 * 1246
def Mwstep4 : (ZMod 1249)[X] := 859 + X * 180 + X ^ 2 * 1097 + X ^ 3 * 92 + X ^ 4 * 203 + X ^ 5 * 905 + X ^ 6 * 394 + X ^ 7 * 1174 + X ^ 8 * 140 + X ^ 9 * 1240 + X ^ 10 * 106 + X ^ 11 * 1057 + X ^ 12 * 678 + X ^ 13 * 309 + X ^ 14 * 540 + X ^ 15 * 1110 + X ^ 16 * 1234 + X ^ 17 * 669 + X ^ 18 * 1246
theorem wstep4 : Lwstep4 = Mwstep4 := by
  have hL : Lwstep4.natDegree ≤ 18 := by unfold Lwstep4; compute_degree!
  have hR : Mwstep4.natDegree ≤ 18 := by unfold Mwstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep4, Mwstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep5 : (ZMod 1249)[X] := 203 + X * 766 + X ^ 2 * 287 + X ^ 3 * 114 + X ^ 4 * 1168 + X ^ 5 * 668 + X ^ 6 * 1015 + X ^ 7 * 129 + X ^ 8 * 466 + X ^ 9 * 653 + X ^ 10 * 476 + X ^ 11 * 904 + X ^ 12 * 727 + X ^ 13 * 685 + X ^ 14 * 172 + X ^ 15 * 606 + X ^ 16 * 849 + X ^ 17 * 191 + X ^ 18 * 498
def Mwstep5 : (ZMod 1249)[X] := 203 + X * 766 + X ^ 2 * 287 + X ^ 3 * 114 + X ^ 4 * 1168 + X ^ 5 * 668 + X ^ 6 * 1015 + X ^ 7 * 129 + X ^ 8 * 466 + X ^ 9 * 653 + X ^ 10 * 476 + X ^ 11 * 904 + X ^ 12 * 727 + X ^ 13 * 685 + X ^ 14 * 172 + X ^ 15 * 606 + X ^ 16 * 849 + X ^ 17 * 191 + X ^ 18 * 498
theorem wstep5 : Lwstep5 = Mwstep5 := by
  have hL : Lwstep5.natDegree ≤ 18 := by unfold Lwstep5; compute_degree!
  have hR : Mwstep5.natDegree ≤ 18 := by unfold Mwstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep5, Mwstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep6 : (ZMod 1249)[X] := 810 + X * 241 + X ^ 2 * 21 + X ^ 3 * 515 + X ^ 4 * 769 + X ^ 5 * 826 + X ^ 6 * 921 + X ^ 7 * 908 + X ^ 8 * 1054 + X ^ 9 * 176 + X ^ 10 * 27 + X ^ 11 * 559 + X ^ 12 * 612 + X ^ 13 * 34 + X ^ 14 * 1199 + X ^ 15 * 839 + X ^ 16 * 1173 + X ^ 17 * 249 + X ^ 18 * 1197
def Mwstep6 : (ZMod 1249)[X] := 810 + X * 241 + X ^ 2 * 21 + X ^ 3 * 515 + X ^ 4 * 769 + X ^ 5 * 826 + X ^ 6 * 921 + X ^ 7 * 908 + X ^ 8 * 1054 + X ^ 9 * 176 + X ^ 10 * 27 + X ^ 11 * 559 + X ^ 12 * 612 + X ^ 13 * 34 + X ^ 14 * 1199 + X ^ 15 * 839 + X ^ 16 * 1173 + X ^ 17 * 249 + X ^ 18 * 1197
theorem wstep6 : Lwstep6 = Mwstep6 := by
  have hL : Lwstep6.natDegree ≤ 18 := by unfold Lwstep6; compute_degree!
  have hR : Mwstep6.natDegree ≤ 18 := by unfold Mwstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep6, Mwstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep7 : (ZMod 1249)[X] := 237 + X * 828 + X ^ 2 * 579 + X ^ 3 * 550 + X ^ 4 * 1150 + X ^ 5 * 590 + X ^ 6 * 517 + X ^ 7 * 235 + X ^ 8 * 1170 + X ^ 9 * 248 + X ^ 10 * 761 + X ^ 11 * 7 + X ^ 12 * 861 + X ^ 13 * 261 + X ^ 14 * 305 + X ^ 15 * 820 + X ^ 16 * 504 + X ^ 17 * 128 + X ^ 18 * 888
def Mwstep7 : (ZMod 1249)[X] := 237 + X * 828 + X ^ 2 * 579 + X ^ 3 * 550 + X ^ 4 * 1150 + X ^ 5 * 590 + X ^ 6 * 517 + X ^ 7 * 235 + X ^ 8 * 1170 + X ^ 9 * 248 + X ^ 10 * 761 + X ^ 11 * 7 + X ^ 12 * 861 + X ^ 13 * 261 + X ^ 14 * 305 + X ^ 15 * 820 + X ^ 16 * 504 + X ^ 17 * 128 + X ^ 18 * 888
theorem wstep7 : Lwstep7 = Mwstep7 := by
  have hL : Lwstep7.natDegree ≤ 18 := by unfold Lwstep7; compute_degree!
  have hR : Mwstep7.natDegree ≤ 18 := by unfold Mwstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep7, Mwstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep8 : (ZMod 1249)[X] := 399 + X * 1208 + X ^ 2 * 71 + X ^ 3 * 190 + X ^ 4 * 1006 + X ^ 5 * 375 + X ^ 6 * 497 + X ^ 7 * 178 + X ^ 8 * 16 + X ^ 9 * 298 + X ^ 10 * 1078 + X ^ 11 * 512 + X ^ 12 * 640 + X ^ 13 * 576 + X ^ 14 * 3 + X ^ 15 * 477 + X ^ 16 * 591 + X ^ 17 * 546 + X ^ 18 * 34
def Mwstep8 : (ZMod 1249)[X] := 399 + X * 1208 + X ^ 2 * 71 + X ^ 3 * 190 + X ^ 4 * 1006 + X ^ 5 * 375 + X ^ 6 * 497 + X ^ 7 * 178 + X ^ 8 * 16 + X ^ 9 * 298 + X ^ 10 * 1078 + X ^ 11 * 512 + X ^ 12 * 640 + X ^ 13 * 576 + X ^ 14 * 3 + X ^ 15 * 477 + X ^ 16 * 591 + X ^ 17 * 546 + X ^ 18 * 34
theorem wstep8 : Lwstep8 = Mwstep8 := by
  have hL : Lwstep8.natDegree ≤ 18 := by unfold Lwstep8; compute_degree!
  have hR : Mwstep8.natDegree ≤ 18 := by unfold Mwstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep8, Mwstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lwstep9 : (ZMod 1249)[X] := 638 + X * 1176 + X ^ 2 * 856 + X ^ 3 * 298 + X ^ 4 * 50 + X ^ 5 * 427 + X ^ 6 * 1121 + X ^ 7 * 749 + X ^ 8 * 206 + X ^ 9 * 859 + X ^ 10 * 644 + X ^ 11 * 211 + X ^ 12 * 929 + X ^ 13 * 1247 + X ^ 14 * 1207 + X ^ 15 * 874 + X ^ 16 * 355 + X ^ 17 * 939 + X ^ 18 * 943
def Mwstep9 : (ZMod 1249)[X] := 638 + X * 1176 + X ^ 2 * 856 + X ^ 3 * 298 + X ^ 4 * 50 + X ^ 5 * 427 + X ^ 6 * 1121 + X ^ 7 * 749 + X ^ 8 * 206 + X ^ 9 * 859 + X ^ 10 * 644 + X ^ 11 * 211 + X ^ 12 * 929 + X ^ 13 * 1247 + X ^ 14 * 1207 + X ^ 15 * 874 + X ^ 16 * 355 + X ^ 17 * 939 + X ^ 18 * 943
theorem wstep9 : Lwstep9 = Mwstep9 := by
  have hL : Lwstep9.natDegree ≤ 18 := by unfold Lwstep9; compute_degree!
  have hR : Mwstep9.natDegree ≤ 18 := by unfold Mwstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lwstep9, Mwstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2562Batch3Actual

end