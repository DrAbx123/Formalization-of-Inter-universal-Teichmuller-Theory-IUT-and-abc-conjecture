import tmp.sheaf.xif.paper.S2564Batch5Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2564Batch5Actual

namespace LeanFormal.IUT.XiFPaper.S2565Batch6Actual

def F0 : (ZMod 1249)[X] := 1194 + X * 810 + X ^ 2 * 856 + X ^ 3 * 203 + X ^ 4 * 881 + X ^ 5 * 314 + X ^ 6 * 738 + X ^ 7 * 1237 + X ^ 8 * 176 + X ^ 9 * 1189
def F1 : (ZMod 1249)[X] := 626 + X * 171 + X ^ 2 * 845 + X ^ 3 * 75 + X ^ 4 * 1087 + X ^ 5 * 774 + X ^ 6 * 366 + X ^ 7 * 846 + X ^ 8 * 661 + X ^ 9 * 47
def F2 : (ZMod 1249)[X] := 223 + X * 447 + X ^ 2 * 1199 + X ^ 3 * 1197 + X ^ 4 * 702 + X ^ 5 * 831 + X ^ 6 * 1140 + X ^ 7 * 1056 + X ^ 8 * 1219 + X ^ 9 * 170
def F3 : (ZMod 1249)[X] := 922 + X * 420 + X ^ 2 * 897 + X ^ 3 * 1062 + X ^ 4 * 291 + X ^ 5 * 556 + X ^ 6 * 184 + X ^ 7 * 25 + X ^ 8 * 364 + X ^ 9 * 261
def F4 : (ZMod 1249)[X] := 155 + X * 74 + X ^ 2 * 323 + X ^ 3 * 371 + X ^ 4 * 198 + X ^ 5 * 656 + X ^ 6 * 372 + X ^ 7 * 117 + X ^ 8 * 861 + X ^ 9 * 690
def F5 : (ZMod 1249)[X] := 238 + X * 329 + X ^ 2 * 498 + X ^ 3 * 782 + X ^ 4 * 1092 + X ^ 5 * 1061 + X ^ 6 * 453 + X ^ 7 * 472 + X ^ 8 * 922 + X ^ 9 * 770
def F6 : (ZMod 1249)[X] := 495 + X * 151 + X ^ 2 * 112 + X ^ 3 * 865 + X ^ 4 * 1200 + X ^ 5 * 441 + X ^ 6 * 733 + X ^ 7 * 1067 + X ^ 8 * 449 + X ^ 9 * 793
def F7 : (ZMod 1249)[X] := 866 + X * 826 + X ^ 2 * 502 + X ^ 3 * 1063 + X ^ 4 * 149 + X ^ 5 * 167 + X ^ 6 * 323 + X ^ 7 * 1184 + X ^ 8 * 996 + X ^ 9 * 63
def F8 : (ZMod 1249)[X] := 66 + X * 1144 + X ^ 2 * 541 + X ^ 3 * 701 + X ^ 4 * 901 + X ^ 5 * 1071 + X ^ 6 * 321 + X ^ 7 * 128 + X ^ 8 * 1221 + X ^ 9 * 131
def F9 : (ZMod 1249)[X] := 830 + X * 943 + X ^ 2 * 219 + X ^ 3 * 354 + X ^ 4 * 89 + X ^ 5 * 758 + X ^ 6 * 900 + X ^ 7 * 1166 + X ^ 8 * 1063 + X ^ 9 * 694
def F10 : (ZMod 1249)[X] := 357 + X * 445 + X ^ 2 * 737 + X ^ 3 * 242 + X ^ 4 * 1004 + X ^ 5 * 1090 + X ^ 6 * 679 + X ^ 7 * 975 + X ^ 8 * 711 + X ^ 9 * 1014
def F11 : (ZMod 1249)[X] := 279 + X * 392 + X ^ 2 * 482 + X ^ 3 * 1145 + X ^ 4 * 783 + X ^ 5 * 1187 + X ^ 6 * 1137 + X ^ 7 * 448 + X ^ 8 * 891 + X ^ 9 * 365
def F12 : (ZMod 1249)[X] := 738 + X * 273 + X ^ 2 * 578 + X ^ 3 * 928 + X ^ 4 * 1090 + X ^ 5 * 663 + X ^ 6 * 483 + X ^ 7 * 1181 + X ^ 8 * 503 + X ^ 9 * 166
def F13 : (ZMod 1249)[X] := 994 + X * 437 + X ^ 2 * 1108 + X ^ 3 * 59 + X ^ 4 * 373 + X ^ 5 * 392 + X ^ 6 * 805 + X ^ 7 * 204 + X ^ 8 * 599 + X ^ 9 * 240
def F14 : (ZMod 1249)[X] := 1208 + X * 1151 + X ^ 2 * 1057 + X ^ 3 * 645 + X ^ 4 * 407 + X ^ 5 * 114 + X ^ 6 * 918 + X ^ 7 * 746 + X ^ 8 * 998 + X ^ 9 * 1067
def F15 : (ZMod 1249)[X] := 176 + X * 1090 + X ^ 2 * 313 + X ^ 3 * 922 + X ^ 4 * 830 + X ^ 5 * 174 + X ^ 6 * 85 + X ^ 7 * 733 + X ^ 8 * 997 + X ^ 9 * 781
def F16 : (ZMod 1249)[X] := 1085 + X * 754 + X ^ 2 * 95 + X ^ 3 * 390 + X ^ 4 * 888 + X ^ 5 * 1009 + X ^ 6 * 513 + X ^ 7 * 642 + X ^ 8 * 266 + X ^ 9 * 447
def F17 : (ZMod 1249)[X] := 1094 + X * 912 + X ^ 2 * 1121 + X ^ 3 * 387 + X ^ 4 * 145 + X ^ 5 * 1211 + X ^ 6 * 291 + X ^ 7 * 672 + X ^ 8 * 1142 + X ^ 9 * 978
def F18 : (ZMod 1249)[X] := 1216 + X * 331 + X ^ 2 * 278 + X ^ 3 * 582 + X ^ 4 * 778 + X ^ 5 * 897 + X ^ 6 * 168 + X ^ 7 * 698 + X ^ 8 * 790 + X ^ 9 * 994
def Lfstep0 : (ZMod 1249)[X] := 527 + X * 828 + X ^ 2 * 1139 + X ^ 3 * 482 + X ^ 4 * 458 + X ^ 5 * 359 + X ^ 6 * 1063 + X ^ 7 * 59 + X ^ 8 * 5 + X ^ 9 * 1221 + X ^ 10 * 721 + X ^ 11 * 135 + X ^ 12 * 1018 + X ^ 13 * 835 + X ^ 14 * 1167 + X ^ 15 * 891 + X ^ 16 * 1191 + X ^ 17 * 113 + X ^ 18 * 1102
def Mfstep0 : (ZMod 1249)[X] := 527 + X * 828 + X ^ 2 * 1139 + X ^ 3 * 482 + X ^ 4 * 458 + X ^ 5 * 359 + X ^ 6 * 1063 + X ^ 7 * 59 + X ^ 8 * 5 + X ^ 9 * 1221 + X ^ 10 * 721 + X ^ 11 * 135 + X ^ 12 * 1018 + X ^ 13 * 835 + X ^ 14 * 1167 + X ^ 15 * 891 + X ^ 16 * 1191 + X ^ 17 * 113 + X ^ 18 * 1102
theorem fstep0 : Lfstep0 = Mfstep0 := by
  have hL : Lfstep0.natDegree ≤ 18 := by unfold Lfstep0; compute_degree!
  have hR : Mfstep0.natDegree ≤ 18 := by unfold Mfstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep0, Mfstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep1 : (ZMod 1249)[X] := 939 + X * 513 + X ^ 2 * 551 + X ^ 3 * 696 + X ^ 4 * 1030 + X ^ 5 * 1226 + X ^ 6 * 149 + X ^ 7 * 100 + X ^ 8 * 541 + X ^ 9 * 1235 + X ^ 10 * 699 + X ^ 11 * 171 + X ^ 12 * 1189 + X ^ 13 * 1074 + X ^ 14 * 842 + X ^ 15 * 1238 + X ^ 16 * 608 + X ^ 17 * 933 + X ^ 18 * 960
def Mfstep1 : (ZMod 1249)[X] := 939 + X * 513 + X ^ 2 * 551 + X ^ 3 * 696 + X ^ 4 * 1030 + X ^ 5 * 1226 + X ^ 6 * 149 + X ^ 7 * 100 + X ^ 8 * 541 + X ^ 9 * 1235 + X ^ 10 * 699 + X ^ 11 * 171 + X ^ 12 * 1189 + X ^ 13 * 1074 + X ^ 14 * 842 + X ^ 15 * 1238 + X ^ 16 * 608 + X ^ 17 * 933 + X ^ 18 * 960
theorem fstep1 : Lfstep1 = Mfstep1 := by
  have hL : Lfstep1.natDegree ≤ 18 := by unfold Lfstep1; compute_degree!
  have hR : Mfstep1.natDegree ≤ 18 := by unfold Mfstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep1, Mfstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep2 : (ZMod 1249)[X] := 1018 + X * 771 + X ^ 2 * 151 + X ^ 3 * 803 + X ^ 4 * 569 + X ^ 5 * 467 + X ^ 6 * 1055 + X ^ 7 * 96 + X ^ 8 * 293 + X ^ 9 * 1107 + X ^ 10 * 647 + X ^ 11 * 1116 + X ^ 12 * 1019 + X ^ 13 * 1078 + X ^ 14 * 340 + X ^ 15 * 749 + X ^ 16 * 228 + X ^ 17 * 1041 + X ^ 18 * 173
def Mfstep2 : (ZMod 1249)[X] := 1018 + X * 771 + X ^ 2 * 151 + X ^ 3 * 803 + X ^ 4 * 569 + X ^ 5 * 467 + X ^ 6 * 1055 + X ^ 7 * 96 + X ^ 8 * 293 + X ^ 9 * 1107 + X ^ 10 * 647 + X ^ 11 * 1116 + X ^ 12 * 1019 + X ^ 13 * 1078 + X ^ 14 * 340 + X ^ 15 * 749 + X ^ 16 * 228 + X ^ 17 * 1041 + X ^ 18 * 173
theorem fstep2 : Lfstep2 = Mfstep2 := by
  have hL : Lfstep2.natDegree ≤ 18 := by unfold Lfstep2; compute_degree!
  have hR : Mfstep2.natDegree ≤ 18 := by unfold Mfstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep2, Mfstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep3 : (ZMod 1249)[X] := 764 + X * 100 + X ^ 2 * 683 + X ^ 3 * 229 + X ^ 4 * 81 + X ^ 5 * 1223 + X ^ 6 * 700 + X ^ 7 * 162 + X ^ 8 * 1018 + X ^ 9 * 40 + X ^ 10 * 154 + X ^ 11 * 447 + X ^ 12 * 1030 + X ^ 13 * 73 + X ^ 14 * 149 + X ^ 15 * 589 + X ^ 16 * 662 + X ^ 17 * 160 + X ^ 18 * 675
def Mfstep3 : (ZMod 1249)[X] := 764 + X * 100 + X ^ 2 * 683 + X ^ 3 * 229 + X ^ 4 * 81 + X ^ 5 * 1223 + X ^ 6 * 700 + X ^ 7 * 162 + X ^ 8 * 1018 + X ^ 9 * 40 + X ^ 10 * 154 + X ^ 11 * 447 + X ^ 12 * 1030 + X ^ 13 * 73 + X ^ 14 * 149 + X ^ 15 * 589 + X ^ 16 * 662 + X ^ 17 * 160 + X ^ 18 * 675
theorem fstep3 : Lfstep3 = Mfstep3 := by
  have hL : Lfstep3.natDegree ≤ 18 := by unfold Lfstep3; compute_degree!
  have hR : Mfstep3.natDegree ≤ 18 := by unfold Mfstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep3, Mfstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep4 : (ZMod 1249)[X] := 294 + X * 458 + X ^ 2 * 690 + X ^ 3 * 444 + X ^ 4 * 793 + X ^ 5 * 208 + X ^ 6 * 839 + X ^ 7 * 48 + X ^ 8 * 85 + X ^ 9 * 972 + X ^ 10 * 97 + X ^ 11 * 294 + X ^ 12 * 740 + X ^ 13 * 1112 + X ^ 14 * 801 + X ^ 15 * 406 + X ^ 16 * 1003 + X ^ 17 * 381 + X ^ 18 * 231
def Mfstep4 : (ZMod 1249)[X] := 294 + X * 458 + X ^ 2 * 690 + X ^ 3 * 444 + X ^ 4 * 793 + X ^ 5 * 208 + X ^ 6 * 839 + X ^ 7 * 48 + X ^ 8 * 85 + X ^ 9 * 972 + X ^ 10 * 97 + X ^ 11 * 294 + X ^ 12 * 740 + X ^ 13 * 1112 + X ^ 14 * 801 + X ^ 15 * 406 + X ^ 16 * 1003 + X ^ 17 * 381 + X ^ 18 * 231
theorem fstep4 : Lfstep4 = Mfstep4 := by
  have hL : Lfstep4.natDegree ≤ 18 := by unfold Lfstep4; compute_degree!
  have hR : Mfstep4.natDegree ≤ 18 := by unfold Mfstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep4, Mfstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep5 : (ZMod 1249)[X] := 439 + X * 479 + X ^ 2 * 565 + X ^ 3 * 476 + X ^ 4 * 878 + X ^ 5 * 297 + X ^ 6 * 14 + X ^ 7 * 22 + X ^ 8 * 748 + X ^ 9 * 102 + X ^ 10 * 428 + X ^ 11 * 655 + X ^ 12 * 763 + X ^ 13 * 301 + X ^ 14 * 461 + X ^ 15 * 493 + X ^ 16 * 726 + X ^ 17 * 1016 + X ^ 18 * 874
def Mfstep5 : (ZMod 1249)[X] := 439 + X * 479 + X ^ 2 * 565 + X ^ 3 * 476 + X ^ 4 * 878 + X ^ 5 * 297 + X ^ 6 * 14 + X ^ 7 * 22 + X ^ 8 * 748 + X ^ 9 * 102 + X ^ 10 * 428 + X ^ 11 * 655 + X ^ 12 * 763 + X ^ 13 * 301 + X ^ 14 * 461 + X ^ 15 * 493 + X ^ 16 * 726 + X ^ 17 * 1016 + X ^ 18 * 874
theorem fstep5 : Lfstep5 = Mfstep5 := by
  have hL : Lfstep5.natDegree ≤ 18 := by unfold Lfstep5; compute_degree!
  have hR : Mfstep5.natDegree ≤ 18 := by unfold Mfstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep5, Mfstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep6 : (ZMod 1249)[X] := 221 + X * 859 + X ^ 2 * 38 + X ^ 3 * 886 + X ^ 4 * 444 + X ^ 5 * 1044 + X ^ 6 * 1128 + X ^ 7 * 244 + X ^ 8 * 125 + X ^ 9 * 207 + X ^ 10 * 467 + X ^ 11 * 40 + X ^ 12 * 1017 + X ^ 13 * 283 + X ^ 14 * 647 + X ^ 15 * 1151 + X ^ 16 * 379 + X ^ 17 * 184 + X ^ 18 * 602
def Mfstep6 : (ZMod 1249)[X] := 221 + X * 859 + X ^ 2 * 38 + X ^ 3 * 886 + X ^ 4 * 444 + X ^ 5 * 1044 + X ^ 6 * 1128 + X ^ 7 * 244 + X ^ 8 * 125 + X ^ 9 * 207 + X ^ 10 * 467 + X ^ 11 * 40 + X ^ 12 * 1017 + X ^ 13 * 283 + X ^ 14 * 647 + X ^ 15 * 1151 + X ^ 16 * 379 + X ^ 17 * 184 + X ^ 18 * 602
theorem fstep6 : Lfstep6 = Mfstep6 := by
  have hL : Lfstep6.natDegree ≤ 18 := by unfold Lfstep6; compute_degree!
  have hR : Mfstep6.natDegree ≤ 18 := by unfold Mfstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep6, Mfstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep7 : (ZMod 1249)[X] := 556 + X * 527 + X ^ 2 * 482 + X ^ 3 * 58 + X ^ 4 * 462 + X ^ 5 * 177 + X ^ 6 * 328 + X ^ 7 * 1182 + X ^ 8 * 1083 + X ^ 9 * 154 + X ^ 10 * 885 + X ^ 11 * 1076 + X ^ 12 * 26 + X ^ 13 * 945 + X ^ 14 * 468 + X ^ 15 * 1146 + X ^ 16 * 863 + X ^ 17 * 596 + X ^ 18 * 222
def Mfstep7 : (ZMod 1249)[X] := 556 + X * 527 + X ^ 2 * 482 + X ^ 3 * 58 + X ^ 4 * 462 + X ^ 5 * 177 + X ^ 6 * 328 + X ^ 7 * 1182 + X ^ 8 * 1083 + X ^ 9 * 154 + X ^ 10 * 885 + X ^ 11 * 1076 + X ^ 12 * 26 + X ^ 13 * 945 + X ^ 14 * 468 + X ^ 15 * 1146 + X ^ 16 * 863 + X ^ 17 * 596 + X ^ 18 * 222
theorem fstep7 : Lfstep7 = Mfstep7 := by
  have hL : Lfstep7.natDegree ≤ 18 := by unfold Lfstep7; compute_degree!
  have hR : Mfstep7.natDegree ≤ 18 := by unfold Mfstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep7, Mfstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep8 : (ZMod 1249)[X] := 609 + X * 1128 + X ^ 2 * 3 + X ^ 3 * 155 + X ^ 4 * 864 + X ^ 5 * 1212 + X ^ 6 * 1022 + X ^ 7 * 908 + X ^ 8 * 944 + X ^ 9 * 1186 + X ^ 10 * 1111 + X ^ 11 * 291 + X ^ 12 * 831 + X ^ 13 * 968 + X ^ 14 * 483 + X ^ 15 * 745 + X ^ 16 * 597 + X ^ 17 * 158 + X ^ 18 * 924
def Mfstep8 : (ZMod 1249)[X] := 609 + X * 1128 + X ^ 2 * 3 + X ^ 3 * 155 + X ^ 4 * 864 + X ^ 5 * 1212 + X ^ 6 * 1022 + X ^ 7 * 908 + X ^ 8 * 944 + X ^ 9 * 1186 + X ^ 10 * 1111 + X ^ 11 * 291 + X ^ 12 * 831 + X ^ 13 * 968 + X ^ 14 * 483 + X ^ 15 * 745 + X ^ 16 * 597 + X ^ 17 * 158 + X ^ 18 * 924
theorem fstep8 : Lfstep8 = Mfstep8 := by
  have hL : Lfstep8.natDegree ≤ 18 := by unfold Lfstep8; compute_degree!
  have hR : Mfstep8.natDegree ≤ 18 := by unfold Mfstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep8, Mfstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep9 : (ZMod 1249)[X] := 701 + X * 383 + X ^ 2 * 42 + X ^ 3 * 225 + X ^ 4 * 286 + X ^ 5 * 1201 + X ^ 6 * 358 + X ^ 7 * 1200 + X ^ 8 * 116 + X ^ 9 * 744 + X ^ 10 * 1189 + X ^ 11 * 628 + X ^ 12 * 830 + X ^ 13 * 659 + X ^ 14 * 1022 + X ^ 15 * 1100 + X ^ 16 * 577 + X ^ 17 * 375 + X ^ 18 * 771
def Mfstep9 : (ZMod 1249)[X] := 701 + X * 383 + X ^ 2 * 42 + X ^ 3 * 225 + X ^ 4 * 286 + X ^ 5 * 1201 + X ^ 6 * 358 + X ^ 7 * 1200 + X ^ 8 * 116 + X ^ 9 * 744 + X ^ 10 * 1189 + X ^ 11 * 628 + X ^ 12 * 830 + X ^ 13 * 659 + X ^ 14 * 1022 + X ^ 15 * 1100 + X ^ 16 * 577 + X ^ 17 * 375 + X ^ 18 * 771
theorem fstep9 : Lfstep9 = Mfstep9 := by
  have hL : Lfstep9.natDegree ≤ 18 := by unfold Lfstep9; compute_degree!
  have hR : Mfstep9.natDegree ≤ 18 := by unfold Mfstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep9, Mfstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep10 : (ZMod 1249)[X] := 51 + X * 484 + X ^ 2 * 1072 + X ^ 3 * 631 + X ^ 4 * 336 + X ^ 5 * 152 + X ^ 6 * 762 + X ^ 7 * 772 + X ^ 8 * 1207 + X ^ 9 * 544 + X ^ 10 * 388 + X ^ 11 * 1004 + X ^ 12 * 1111 + X ^ 13 * 323 + X ^ 14 * 1236 + X ^ 15 * 674 + X ^ 16 * 1058 + X ^ 17 * 562 + X ^ 18 * 269
def Mfstep10 : (ZMod 1249)[X] := 51 + X * 484 + X ^ 2 * 1072 + X ^ 3 * 631 + X ^ 4 * 336 + X ^ 5 * 152 + X ^ 6 * 762 + X ^ 7 * 772 + X ^ 8 * 1207 + X ^ 9 * 544 + X ^ 10 * 388 + X ^ 11 * 1004 + X ^ 12 * 1111 + X ^ 13 * 323 + X ^ 14 * 1236 + X ^ 15 * 674 + X ^ 16 * 1058 + X ^ 17 * 562 + X ^ 18 * 269
theorem fstep10 : Lfstep10 = Mfstep10 := by
  have hL : Lfstep10.natDegree ≤ 18 := by unfold Lfstep10; compute_degree!
  have hR : Mfstep10.natDegree ≤ 18 := by unfold Mfstep10; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep10, Mfstep10, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep11 : (ZMod 1249)[X] := 403 + X * 161 + X ^ 2 * 458 + X ^ 3 * 112 + X ^ 4 * 672 + X ^ 5 * 653 + X ^ 6 * 48 + X ^ 7 * 745 + X ^ 8 * 21 + X ^ 9 * 49 + X ^ 10 * 1056 + X ^ 11 * 194 + X ^ 12 * 1149 + X ^ 13 * 1042 + X ^ 14 * 824 + X ^ 15 * 899 + X ^ 16 * 568 + X ^ 17 * 950 + X ^ 18 * 831
def Mfstep11 : (ZMod 1249)[X] := 403 + X * 161 + X ^ 2 * 458 + X ^ 3 * 112 + X ^ 4 * 672 + X ^ 5 * 653 + X ^ 6 * 48 + X ^ 7 * 745 + X ^ 8 * 21 + X ^ 9 * 49 + X ^ 10 * 1056 + X ^ 11 * 194 + X ^ 12 * 1149 + X ^ 13 * 1042 + X ^ 14 * 824 + X ^ 15 * 899 + X ^ 16 * 568 + X ^ 17 * 950 + X ^ 18 * 831
theorem fstep11 : Lfstep11 = Mfstep11 := by
  have hL : Lfstep11.natDegree ≤ 18 := by unfold Lfstep11; compute_degree!
  have hR : Mfstep11.natDegree ≤ 18 := by unfold Mfstep11; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep11, Mfstep11, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep12 : (ZMod 1249)[X] := 80 + X * 770 + X ^ 2 * 899 + X ^ 3 * 415 + X ^ 4 * 323 + X ^ 5 * 1114 + X ^ 6 * 1188 + X ^ 7 * 182 + X ^ 8 * 224 + X ^ 9 * 62 + X ^ 10 * 37 + X ^ 11 * 227 + X ^ 12 * 246 + X ^ 13 * 191 + X ^ 14 * 1206 + X ^ 15 * 771 + X ^ 16 * 617 + X ^ 17 * 879 + X ^ 18 * 78
def Mfstep12 : (ZMod 1249)[X] := 80 + X * 770 + X ^ 2 * 899 + X ^ 3 * 415 + X ^ 4 * 323 + X ^ 5 * 1114 + X ^ 6 * 1188 + X ^ 7 * 182 + X ^ 8 * 224 + X ^ 9 * 62 + X ^ 10 * 37 + X ^ 11 * 227 + X ^ 12 * 246 + X ^ 13 * 191 + X ^ 14 * 1206 + X ^ 15 * 771 + X ^ 16 * 617 + X ^ 17 * 879 + X ^ 18 * 78
theorem fstep12 : Lfstep12 = Mfstep12 := by
  have hL : Lfstep12.natDegree ≤ 18 := by unfold Lfstep12; compute_degree!
  have hR : Mfstep12.natDegree ≤ 18 := by unfold Mfstep12; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep12, Mfstep12, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep13 : (ZMod 1249)[X] := 77 + X * 701 + X ^ 2 * 589 + X ^ 3 * 303 + X ^ 4 * 1121 + X ^ 5 * 781 + X ^ 6 * 217 + X ^ 7 * 926 + X ^ 8 * 1045 + X ^ 9 * 355 + X ^ 10 * 1013 + X ^ 11 * 685 + X ^ 12 * 412 + X ^ 13 * 378 + X ^ 14 * 122 + X ^ 15 * 47 + X ^ 16 * 836 + X ^ 17 * 250 + X ^ 18 * 146
def Mfstep13 : (ZMod 1249)[X] := 77 + X * 701 + X ^ 2 * 589 + X ^ 3 * 303 + X ^ 4 * 1121 + X ^ 5 * 781 + X ^ 6 * 217 + X ^ 7 * 926 + X ^ 8 * 1045 + X ^ 9 * 355 + X ^ 10 * 1013 + X ^ 11 * 685 + X ^ 12 * 412 + X ^ 13 * 378 + X ^ 14 * 122 + X ^ 15 * 47 + X ^ 16 * 836 + X ^ 17 * 250 + X ^ 18 * 146
theorem fstep13 : Lfstep13 = Mfstep13 := by
  have hL : Lfstep13.natDegree ≤ 18 := by unfold Lfstep13; compute_degree!
  have hR : Mfstep13.natDegree ≤ 18 := by unfold Mfstep13; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep13, Mfstep13, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep14 : (ZMod 1249)[X] := 432 + X * 542 + X ^ 2 * 368 + X ^ 3 * 979 + X ^ 4 * 721 + X ^ 5 * 430 + X ^ 6 * 996 + X ^ 7 * 346 + X ^ 8 * 680 + X ^ 9 * 516 + X ^ 10 * 1128 + X ^ 11 * 596 + X ^ 12 * 427 + X ^ 13 * 212 + X ^ 14 * 477 + X ^ 15 * 788 + X ^ 16 * 40 + X ^ 17 * 187 + X ^ 18 * 650
def Mfstep14 : (ZMod 1249)[X] := 432 + X * 542 + X ^ 2 * 368 + X ^ 3 * 979 + X ^ 4 * 721 + X ^ 5 * 430 + X ^ 6 * 996 + X ^ 7 * 346 + X ^ 8 * 680 + X ^ 9 * 516 + X ^ 10 * 1128 + X ^ 11 * 596 + X ^ 12 * 427 + X ^ 13 * 212 + X ^ 14 * 477 + X ^ 15 * 788 + X ^ 16 * 40 + X ^ 17 * 187 + X ^ 18 * 650
theorem fstep14 : Lfstep14 = Mfstep14 := by
  have hL : Lfstep14.natDegree ≤ 18 := by unfold Lfstep14; compute_degree!
  have hR : Mfstep14.natDegree ≤ 18 := by unfold Mfstep14; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep14, Mfstep14, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep15 : (ZMod 1249)[X] := 1000 + X * 237 + X ^ 2 * 565 + X ^ 3 * 190 + X ^ 4 * 760 + X ^ 5 * 1029 + X ^ 6 * 328 + X ^ 7 * 677 + X ^ 8 * 511 + X ^ 9 * 494 + X ^ 10 * 312 + X ^ 11 * 345 + X ^ 12 * 181 + X ^ 13 * 691 + X ^ 14 * 600 + X ^ 15 * 648 + X ^ 16 * 667 + X ^ 17 * 1060 + X ^ 18 * 449
def Mfstep15 : (ZMod 1249)[X] := 1000 + X * 237 + X ^ 2 * 565 + X ^ 3 * 190 + X ^ 4 * 760 + X ^ 5 * 1029 + X ^ 6 * 328 + X ^ 7 * 677 + X ^ 8 * 511 + X ^ 9 * 494 + X ^ 10 * 312 + X ^ 11 * 345 + X ^ 12 * 181 + X ^ 13 * 691 + X ^ 14 * 600 + X ^ 15 * 648 + X ^ 16 * 667 + X ^ 17 * 1060 + X ^ 18 * 449
theorem fstep15 : Lfstep15 = Mfstep15 := by
  have hL : Lfstep15.natDegree ≤ 18 := by unfold Lfstep15; compute_degree!
  have hR : Mfstep15.natDegree ≤ 18 := by unfold Mfstep15; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep15, Mfstep15, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep16 : (ZMod 1249)[X] := 667 + X * 1239 + X ^ 2 * 286 + X ^ 3 * 352 + X ^ 4 * 1125 + X ^ 5 * 618 + X ^ 6 * 468 + X ^ 7 * 1036 + X ^ 8 * 966 + X ^ 9 * 672 + X ^ 10 * 820 + X ^ 11 * 1061 + X ^ 12 * 456 + X ^ 13 * 944 + X ^ 14 * 896 + X ^ 15 * 806 + X ^ 16 * 220 + X ^ 17 * 494 + X ^ 18 * 1218
def Mfstep16 : (ZMod 1249)[X] := 667 + X * 1239 + X ^ 2 * 286 + X ^ 3 * 352 + X ^ 4 * 1125 + X ^ 5 * 618 + X ^ 6 * 468 + X ^ 7 * 1036 + X ^ 8 * 966 + X ^ 9 * 672 + X ^ 10 * 820 + X ^ 11 * 1061 + X ^ 12 * 456 + X ^ 13 * 944 + X ^ 14 * 896 + X ^ 15 * 806 + X ^ 16 * 220 + X ^ 17 * 494 + X ^ 18 * 1218
theorem fstep16 : Lfstep16 = Mfstep16 := by
  have hL : Lfstep16.natDegree ≤ 18 := by unfold Lfstep16; compute_degree!
  have hR : Mfstep16.natDegree ≤ 18 := by unfold Mfstep16; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep16, Mfstep16, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lfstep17 : (ZMod 1249)[X] := 294 + X * 803 + X ^ 2 * 871 + X ^ 3 * 25 + X ^ 4 * 364 + X ^ 5 * 1079 + X ^ 6 * 589 + X ^ 7 * 1027 + X ^ 8 * 706 + X ^ 9 * 968 + X ^ 10 * 411 + X ^ 11 * 699 + X ^ 12 * 159 + X ^ 13 * 902 + X ^ 14 * 234 + X ^ 15 * 728 + X ^ 16 * 692 + X ^ 17 * 540 + X ^ 18 * 999
def Mfstep17 : (ZMod 1249)[X] := 294 + X * 803 + X ^ 2 * 871 + X ^ 3 * 25 + X ^ 4 * 364 + X ^ 5 * 1079 + X ^ 6 * 589 + X ^ 7 * 1027 + X ^ 8 * 706 + X ^ 9 * 968 + X ^ 10 * 411 + X ^ 11 * 699 + X ^ 12 * 159 + X ^ 13 * 902 + X ^ 14 * 234 + X ^ 15 * 728 + X ^ 16 * 692 + X ^ 17 * 540 + X ^ 18 * 999
theorem fstep17 : Lfstep17 = Mfstep17 := by
  have hL : Lfstep17.natDegree ≤ 18 := by unfold Lfstep17; compute_degree!
  have hR : Mfstep17.natDegree ≤ 18 := by unfold Mfstep17; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lfstep17, Mfstep17, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2565Batch6Actual

end