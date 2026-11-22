import tmp.sheaf.xif.paper.S2567Batch8Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2567Batch8Actual

namespace LeanFormal.IUT.XiFPaper.S2568Batch9Actual

def P0 : (ZMod 1249)[X] := 1194 + X * 810 + X ^ 2 * 856 + X ^ 3 * 203 + X ^ 4 * 881 + X ^ 5 * 314 + X ^ 6 * 738 + X ^ 7 * 1237 + X ^ 8 * 176 + X ^ 9 * 1189
def P1 : (ZMod 1249)[X] := 238 + X * 329 + X ^ 2 * 498 + X ^ 3 * 782 + X ^ 4 * 1092 + X ^ 5 * 1061 + X ^ 6 * 453 + X ^ 7 * 472 + X ^ 8 * 922 + X ^ 9 * 770
def P2 : (ZMod 1249)[X] := 495 + X * 151 + X ^ 2 * 112 + X ^ 3 * 865 + X ^ 4 * 1200 + X ^ 5 * 441 + X ^ 6 * 733 + X ^ 7 * 1067 + X ^ 8 * 449 + X ^ 9 * 793
def P3 : (ZMod 1249)[X] := 1208 + X * 1151 + X ^ 2 * 1057 + X ^ 3 * 645 + X ^ 4 * 407 + X ^ 5 * 114 + X ^ 6 * 918 + X ^ 7 * 746 + X ^ 8 * 998 + X ^ 9 * 1067
def P4 : (ZMod 1249)[X] := 176 + X * 1090 + X ^ 2 * 313 + X ^ 3 * 922 + X ^ 4 * 830 + X ^ 5 * 174 + X ^ 6 * 85 + X ^ 7 * 733 + X ^ 8 * 997 + X ^ 9 * 781
def P5 : (ZMod 1249)[X] := 607 + X * 523 + X ^ 2 * 428 + X ^ 3 * 414 + X ^ 4 * 312 + X ^ 5 * 371 + X ^ 6 * 775 + X ^ 7 * 438 + X ^ 8 * 1231 + X ^ 9 * 202
def P6 : (ZMod 1249)[X] := 27 + X * 119 + X ^ 2 * 1099 + X ^ 3 * 980 + X ^ 4 * 92 + X ^ 5 * 377 + X ^ 6 * 288 + X ^ 7 * 614 + X ^ 8 * 443 + X ^ 9 * 183
def P7 : (ZMod 1249)[X] := 490 + X * 421 + X ^ 2 * 975 + X ^ 3 * 1142 + X ^ 4 * 466 + X ^ 5 * 1199 + X ^ 6 * 198 + X ^ 7 * 62 + X ^ 8 * 458 + X ^ 9 * 760
def P8 : (ZMod 1249)[X] := 99 + X * 791 + X ^ 2 * 674 + X ^ 3 * 537 + X ^ 4 * 176 + X ^ 5 * 245 + X ^ 6 * 23 + X ^ 7 * 411 + X ^ 8 * 244 + X ^ 9 * 507
def P9 : (ZMod 1249)[X] := 638 + X * 1018 + X ^ 2 * 29 + X ^ 3 * 479 + X ^ 4 * 672 + X ^ 5 * 1097 + X ^ 6 * 460 + X ^ 7 * 941 + X ^ 8 * 757 + X ^ 9 * 986
def P10 : (ZMod 1249)[X] := 774 + X * 1070 + X ^ 2 * 484 + X ^ 3 * 1078 + X ^ 4 * 337 + X ^ 5 * 254 + X ^ 6 * 1020 + X ^ 7 * 43 + X ^ 8 * 1231 + X ^ 9 * 827
def P11 : (ZMod 1249)[X] := 751 + X * 909 + X ^ 2 * 757 + X ^ 3 * 1036 + X ^ 4 * 8 + X ^ 5 * 555 + X ^ 6 * 960 + X ^ 7 * 670 + X ^ 8 * 739 + X ^ 9 * 554
def P12 : (ZMod 1249)[X] := 1122 + X * 816 + X ^ 2 * 776 + X ^ 3 * 761 + X ^ 4 * 503 + X ^ 5 * 828 + X ^ 6 * 994 + X ^ 7 * 215 + X ^ 8 * 593 + X ^ 9 * 415
def P13 : (ZMod 1249)[X] := 863 + X * 476 + X ^ 2 * 443 + X ^ 3 * 303 + X ^ 4 * 126 + X ^ 5 * 1109 + X ^ 6 * 537 + X ^ 7 * 855 + X ^ 8 * 1104 + X ^ 9 * 913
def P14 : (ZMod 1249)[X] := 934 + X * 1084 + X ^ 2 * 365 + X ^ 3 * 289 + X ^ 4 * 720 + X ^ 5 * 235 + X ^ 6 * 880 + X ^ 7 * 176 + X ^ 8 * 1017 + X ^ 9 * 428
def P15 : (ZMod 1249)[X] := 1213 + X * 833 + X ^ 2 * 1024 + X ^ 3 * 1188 + X ^ 4 * 577 + X ^ 5 * 401 + X ^ 6 * 837 + X ^ 7 * 598 + X ^ 8 * 282 + X ^ 9 * 345
def P16 : (ZMod 1249)[X] := 27 + X * 576 + X ^ 2 * 708 + X ^ 3 * 274 + X ^ 4 * 863 + X ^ 5 * 912 + X ^ 6 * 37 + X ^ 7 * 1146 + X ^ 8 * 792 + X ^ 9 * 603
def P17 : (ZMod 1249)[X] := 77 + X * 449 + X ^ 2 * 475 + X ^ 3 * 332 + X ^ 4 * 1068 + X ^ 5 * 1027 + X ^ 6 * 1235 + X ^ 7 * 511 + X ^ 8 * 280 + X ^ 9 * 761
def P18 : (ZMod 1249)[X] := 1137 + X * 265 + X ^ 2 * 270 + X ^ 3 * 966 + X ^ 4 * 853 + X ^ 5 * 865 + X ^ 6 * 967 + X ^ 7 * 26 + X ^ 8 * 984 + X ^ 9 * 570
def P19 : (ZMod 1249)[X] := 523 + X * 694 + X ^ 2 * 1179 + X ^ 3 * 193 + X ^ 4 * 1132 + X ^ 5 * 246 + X ^ 6 * 599 + X ^ 7 * 297 + X ^ 8 * 751 + X ^ 9 * 377
def P20 : (ZMod 1249)[X] := 1201 + X * 260 + X ^ 2 * 1018 + X ^ 3 * 1111 + X ^ 4 * 67 + X ^ 5 * 125 + X ^ 6 * 984 + X ^ 7 * 93 + X ^ 8 * 761 + X ^ 9 * 922
def P21 : (ZMod 1249)[X] := 72 + X * 263 + X ^ 2 * 1063 + X ^ 3 * 802 + X ^ 4 * 665 + X ^ 5 * 586 + X ^ 6 * 1067 + X ^ 7 * 745 + X ^ 8 * 704 + X ^ 9 * 345
def P22 : (ZMod 1249)[X] := 1155 + X * 15 + X ^ 2 * 569 + X ^ 3 * 702 + X ^ 4 * 1130 + X ^ 5 * 609 + X ^ 6 * 82 + X ^ 7 * 200 + X ^ 8 * 1197 + X ^ 9 * 990
def Lmstep0 : (ZMod 1249)[X] := 649 + X * 1074 + X ^ 2 * 682 + X ^ 3 * 860 + X ^ 4 * 884 + X ^ 5 * 302 + X ^ 6 * 299 + X ^ 7 * 668 + X ^ 8 * 1114 + X ^ 9 * 330 + X ^ 10 * 401 + X ^ 11 * 103 + X ^ 12 * 1171 + X ^ 13 * 640 + X ^ 14 * 866 + X ^ 15 * 1078 + X ^ 16 * 1061 + X ^ 17 * 264 + X ^ 18 * 13
def Mmstep0 : (ZMod 1249)[X] := 649 + X * 1074 + X ^ 2 * 682 + X ^ 3 * 860 + X ^ 4 * 884 + X ^ 5 * 302 + X ^ 6 * 299 + X ^ 7 * 668 + X ^ 8 * 1114 + X ^ 9 * 330 + X ^ 10 * 401 + X ^ 11 * 103 + X ^ 12 * 1171 + X ^ 13 * 640 + X ^ 14 * 866 + X ^ 15 * 1078 + X ^ 16 * 1061 + X ^ 17 * 264 + X ^ 18 * 13
theorem mstep0 : Lmstep0 = Mmstep0 := by
  have hL : Lmstep0.natDegree ≤ 18 := by unfold Lmstep0; compute_degree!
  have hR : Mmstep0.natDegree ≤ 18 := by unfold Mmstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep0, Mmstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep1 : (ZMod 1249)[X] := 757 + X * 878 + X ^ 2 * 39 + X ^ 3 * 382 + X ^ 4 * 1200 + X ^ 5 * 1101 + X ^ 6 * 786 + X ^ 7 * 423 + X ^ 8 * 1098 + X ^ 9 * 1069 + X ^ 10 * 302 + X ^ 11 * 986 + X ^ 12 * 236 + X ^ 13 * 107 + X ^ 14 * 315 + X ^ 15 * 718 + X ^ 16 * 137 + X ^ 17 * 1011 + X ^ 18 * 117
def Mmstep1 : (ZMod 1249)[X] := 757 + X * 878 + X ^ 2 * 39 + X ^ 3 * 382 + X ^ 4 * 1200 + X ^ 5 * 1101 + X ^ 6 * 786 + X ^ 7 * 423 + X ^ 8 * 1098 + X ^ 9 * 1069 + X ^ 10 * 302 + X ^ 11 * 986 + X ^ 12 * 236 + X ^ 13 * 107 + X ^ 14 * 315 + X ^ 15 * 718 + X ^ 16 * 137 + X ^ 17 * 1011 + X ^ 18 * 117
theorem mstep1 : Lmstep1 = Mmstep1 := by
  have hL : Lmstep1.natDegree ≤ 18 := by unfold Lmstep1; compute_degree!
  have hR : Mmstep1.natDegree ≤ 18 := by unfold Mmstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep1, Mmstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep2 : (ZMod 1249)[X] := 892 + X * 1102 + X ^ 2 * 646 + X ^ 3 * 108 + X ^ 4 * 919 + X ^ 5 * 1136 + X ^ 6 * 840 + X ^ 7 * 12 + X ^ 8 * 179 + X ^ 9 * 677 + X ^ 10 * 666 + X ^ 11 * 502 + X ^ 12 * 764 + X ^ 13 * 479 + X ^ 14 * 871 + X ^ 15 * 14 + X ^ 16 * 715 + X ^ 17 * 220 + X ^ 18 * 759
def Mmstep2 : (ZMod 1249)[X] := 892 + X * 1102 + X ^ 2 * 646 + X ^ 3 * 108 + X ^ 4 * 919 + X ^ 5 * 1136 + X ^ 6 * 840 + X ^ 7 * 12 + X ^ 8 * 179 + X ^ 9 * 677 + X ^ 10 * 666 + X ^ 11 * 502 + X ^ 12 * 764 + X ^ 13 * 479 + X ^ 14 * 871 + X ^ 15 * 14 + X ^ 16 * 715 + X ^ 17 * 220 + X ^ 18 * 759
theorem mstep2 : Lmstep2 = Mmstep2 := by
  have hL : Lmstep2.natDegree ≤ 18 := by unfold Lmstep2; compute_degree!
  have hR : Mmstep2.natDegree ≤ 18 := by unfold Mmstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep2, Mmstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep3 : (ZMod 1249)[X] := 896 + X * 1145 + X ^ 2 * 750 + X ^ 3 * 252 + X ^ 4 * 323 + X ^ 5 * 61 + X ^ 6 * 637 + X ^ 7 * 998 + X ^ 8 * 1008 + X ^ 9 * 1020 + X ^ 10 * 1121 + X ^ 11 * 1196 + X ^ 12 * 309 + X ^ 13 * 1011 + X ^ 14 * 372 + X ^ 15 * 1146 + X ^ 16 * 29 + X ^ 17 * 15 + X ^ 18 * 73
def Mmstep3 : (ZMod 1249)[X] := 896 + X * 1145 + X ^ 2 * 750 + X ^ 3 * 252 + X ^ 4 * 323 + X ^ 5 * 61 + X ^ 6 * 637 + X ^ 7 * 998 + X ^ 8 * 1008 + X ^ 9 * 1020 + X ^ 10 * 1121 + X ^ 11 * 1196 + X ^ 12 * 309 + X ^ 13 * 1011 + X ^ 14 * 372 + X ^ 15 * 1146 + X ^ 16 * 29 + X ^ 17 * 15 + X ^ 18 * 73
theorem mstep3 : Lmstep3 = Mmstep3 := by
  have hL : Lmstep3.natDegree ≤ 18 := by unfold Lmstep3; compute_degree!
  have hR : Mmstep3.natDegree ≤ 18 := by unfold Mmstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep3, Mmstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep4 : (ZMod 1249)[X] := 292 + X * 1204 + X ^ 2 * 974 + X ^ 3 * 1139 + X ^ 4 * 517 + X ^ 5 * 434 + X ^ 6 * 595 + X ^ 7 * 1194 + X ^ 8 * 204 + X ^ 9 * 388 + X ^ 10 * 1207 + X ^ 11 * 71 + X ^ 12 * 1198 + X ^ 13 * 1177 + X ^ 14 * 990 + X ^ 15 * 1125 + X ^ 16 * 447 + X ^ 17 * 58 + X ^ 18 * 184
def Mmstep4 : (ZMod 1249)[X] := 292 + X * 1204 + X ^ 2 * 974 + X ^ 3 * 1139 + X ^ 4 * 517 + X ^ 5 * 434 + X ^ 6 * 595 + X ^ 7 * 1194 + X ^ 8 * 204 + X ^ 9 * 388 + X ^ 10 * 1207 + X ^ 11 * 71 + X ^ 12 * 1198 + X ^ 13 * 1177 + X ^ 14 * 990 + X ^ 15 * 1125 + X ^ 16 * 447 + X ^ 17 * 58 + X ^ 18 * 184
theorem mstep4 : Lmstep4 = Mmstep4 := by
  have hL : Lmstep4.natDegree ≤ 18 := by unfold Lmstep4; compute_degree!
  have hR : Mmstep4.natDegree ≤ 18 := by unfold Mmstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep4, Mmstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep5 : (ZMod 1249)[X] := 372 + X * 1044 + X ^ 2 * 920 + X ^ 3 * 81 + X ^ 4 * 1006 + X ^ 5 * 840 + X ^ 6 * 41 + X ^ 7 * 501 + X ^ 8 * 816 + X ^ 9 * 784 + X ^ 10 * 619 + X ^ 11 * 353 + X ^ 12 * 1002 + X ^ 13 * 472 + X ^ 14 * 74 + X ^ 15 * 153 + X ^ 16 * 361 + X ^ 17 * 393 + X ^ 18 * 1118
def Mmstep5 : (ZMod 1249)[X] := 372 + X * 1044 + X ^ 2 * 920 + X ^ 3 * 81 + X ^ 4 * 1006 + X ^ 5 * 840 + X ^ 6 * 41 + X ^ 7 * 501 + X ^ 8 * 816 + X ^ 9 * 784 + X ^ 10 * 619 + X ^ 11 * 353 + X ^ 12 * 1002 + X ^ 13 * 472 + X ^ 14 * 74 + X ^ 15 * 153 + X ^ 16 * 361 + X ^ 17 * 393 + X ^ 18 * 1118
theorem mstep5 : Lmstep5 = Mmstep5 := by
  have hL : Lmstep5.natDegree ≤ 18 := by unfold Lmstep5; compute_degree!
  have hR : Mmstep5.natDegree ≤ 18 := by unfold Mmstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep5, Mmstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep6 : (ZMod 1249)[X] := X * 33 + X ^ 2 * 1022 + X ^ 3 * 1070 + X ^ 4 * 465 + X ^ 5 * 804 + X ^ 6 * 1036 + X ^ 7 * 184 + X ^ 8 * 650 + X ^ 9 * 112 + X ^ 10 * 991 + X ^ 11 * 602 + X ^ 12 * 1076 + X ^ 13 * 1198 + X ^ 14 * 368 + X ^ 15 * 1069 + X ^ 16 * 1194 + X ^ 17 * 86 + X ^ 18 * 1013
def Mmstep6 : (ZMod 1249)[X] := X * 33 + X ^ 2 * 1022 + X ^ 3 * 1070 + X ^ 4 * 465 + X ^ 5 * 804 + X ^ 6 * 1036 + X ^ 7 * 184 + X ^ 8 * 650 + X ^ 9 * 112 + X ^ 10 * 991 + X ^ 11 * 602 + X ^ 12 * 1076 + X ^ 13 * 1198 + X ^ 14 * 368 + X ^ 15 * 1069 + X ^ 16 * 1194 + X ^ 17 * 86 + X ^ 18 * 1013
theorem mstep6 : Lmstep6 = Mmstep6 := by
  have hL : Lmstep6.natDegree ≤ 18 := by unfold Lmstep6; compute_degree!
  have hR : Mmstep6.natDegree ≤ 18 := by unfold Mmstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep6, Mmstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep7 : (ZMod 1249)[X] := 220 + X * 857 + X ^ 2 * 737 + X ^ 3 * 652 + X ^ 4 * 546 + X ^ 5 * 229 + X ^ 6 * 854 + X ^ 7 * 1167 + X ^ 8 * 1056 + X ^ 9 * 516 + X ^ 10 * 756 + X ^ 11 * 926 + X ^ 12 * 278 + X ^ 13 * 1161 + X ^ 14 * 895 + X ^ 15 * 110 + X ^ 16 * 540 + X ^ 17 * 321 + X ^ 18 * 686
def Mmstep7 : (ZMod 1249)[X] := 220 + X * 857 + X ^ 2 * 737 + X ^ 3 * 652 + X ^ 4 * 546 + X ^ 5 * 229 + X ^ 6 * 854 + X ^ 7 * 1167 + X ^ 8 * 1056 + X ^ 9 * 516 + X ^ 10 * 756 + X ^ 11 * 926 + X ^ 12 * 278 + X ^ 13 * 1161 + X ^ 14 * 895 + X ^ 15 * 110 + X ^ 16 * 540 + X ^ 17 * 321 + X ^ 18 * 686
theorem mstep7 : Lmstep7 = Mmstep7 := by
  have hL : Lmstep7.natDegree ≤ 18 := by unfold Lmstep7; compute_degree!
  have hR : Mmstep7.natDegree ≤ 18 := by unfold Mmstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep7, Mmstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep8 : (ZMod 1249)[X] := 407 + X * 188 + X ^ 2 * 826 + X ^ 3 * 966 + X ^ 4 * 1184 + X ^ 5 * 777 + X ^ 6 * 198 + X ^ 7 * 1072 + X ^ 8 * 287 + X ^ 9 * 1120 + X ^ 10 * 486 + X ^ 11 * 29 + X ^ 12 * 567 + X ^ 13 * 1115 + X ^ 14 * 1039 + X ^ 15 * 717 + X ^ 16 * 1048 + X ^ 17 * 219 + X ^ 18 * 1233
def Mmstep8 : (ZMod 1249)[X] := 407 + X * 188 + X ^ 2 * 826 + X ^ 3 * 966 + X ^ 4 * 1184 + X ^ 5 * 777 + X ^ 6 * 198 + X ^ 7 * 1072 + X ^ 8 * 287 + X ^ 9 * 1120 + X ^ 10 * 486 + X ^ 11 * 29 + X ^ 12 * 567 + X ^ 13 * 1115 + X ^ 14 * 1039 + X ^ 15 * 717 + X ^ 16 * 1048 + X ^ 17 * 219 + X ^ 18 * 1233
theorem mstep8 : Lmstep8 = Mmstep8 := by
  have hL : Lmstep8.natDegree ≤ 18 := by unfold Lmstep8; compute_degree!
  have hR : Mmstep8.natDegree ≤ 18 := by unfold Mmstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep8, Mmstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep9 : (ZMod 1249)[X] := 1205 + X * 1146 + X ^ 2 * 174 + X ^ 3 * 951 + X ^ 4 * 514 + X ^ 5 * 564 + X ^ 6 * 122 + X ^ 7 * 865 + X ^ 8 * 691 + X ^ 9 * 227 + X ^ 10 * 966 + X ^ 11 * 522 + X ^ 12 * 1038 + X ^ 13 * 538 + X ^ 14 * 251 + X ^ 15 * 27 + X ^ 16 * 338 + X ^ 17 * 1195 + X ^ 18 * 145
def Mmstep9 : (ZMod 1249)[X] := 1205 + X * 1146 + X ^ 2 * 174 + X ^ 3 * 951 + X ^ 4 * 514 + X ^ 5 * 564 + X ^ 6 * 122 + X ^ 7 * 865 + X ^ 8 * 691 + X ^ 9 * 227 + X ^ 10 * 966 + X ^ 11 * 522 + X ^ 12 * 1038 + X ^ 13 * 538 + X ^ 14 * 251 + X ^ 15 * 27 + X ^ 16 * 338 + X ^ 17 * 1195 + X ^ 18 * 145
theorem mstep9 : Lmstep9 = Mmstep9 := by
  have hL : Lmstep9.natDegree ≤ 18 := by unfold Lmstep9; compute_degree!
  have hR : Mmstep9.natDegree ≤ 18 := by unfold Mmstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep9, Mmstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep10 : (ZMod 1249)[X] := 734 + X * 283 + X ^ 2 * 139 + X ^ 3 * 748 + X ^ 4 * 10 + X ^ 5 * 206 + X ^ 6 * 266 + X ^ 7 * 961 + X ^ 8 * 859 + X ^ 9 * 984 + X ^ 10 * 42 + X ^ 11 * 594 + X ^ 12 * 1206 + X ^ 13 * 546 + X ^ 14 * 498 + X ^ 15 * 1105 + X ^ 16 * 727 + X ^ 17 * 1190 + X ^ 18 * 333
def Mmstep10 : (ZMod 1249)[X] := 734 + X * 283 + X ^ 2 * 139 + X ^ 3 * 748 + X ^ 4 * 10 + X ^ 5 * 206 + X ^ 6 * 266 + X ^ 7 * 961 + X ^ 8 * 859 + X ^ 9 * 984 + X ^ 10 * 42 + X ^ 11 * 594 + X ^ 12 * 1206 + X ^ 13 * 546 + X ^ 14 * 498 + X ^ 15 * 1105 + X ^ 16 * 727 + X ^ 17 * 1190 + X ^ 18 * 333
theorem mstep10 : Lmstep10 = Mmstep10 := by
  have hL : Lmstep10.natDegree ≤ 18 := by unfold Lmstep10; compute_degree!
  have hR : Mmstep10.natDegree ≤ 18 := by unfold Mmstep10; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep10, Mmstep10, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep11 : (ZMod 1249)[X] := 283 + X * 361 + X ^ 2 * 1117 + X ^ 3 * 439 + X ^ 4 * 846 + X ^ 5 * 1166 + X ^ 6 * 249 + X ^ 7 * 1004 + X ^ 8 * 430 + X ^ 9 * 1213 + X ^ 10 * 1123 + X ^ 11 * 642 + X ^ 12 * 374 + X ^ 13 * 358 + X ^ 14 * 642 + X ^ 15 * 63 + X ^ 16 * 257 + X ^ 17 * 206 + X ^ 18 * 747
def Mmstep11 : (ZMod 1249)[X] := 283 + X * 361 + X ^ 2 * 1117 + X ^ 3 * 439 + X ^ 4 * 846 + X ^ 5 * 1166 + X ^ 6 * 249 + X ^ 7 * 1004 + X ^ 8 * 430 + X ^ 9 * 1213 + X ^ 10 * 1123 + X ^ 11 * 642 + X ^ 12 * 374 + X ^ 13 * 358 + X ^ 14 * 642 + X ^ 15 * 63 + X ^ 16 * 257 + X ^ 17 * 206 + X ^ 18 * 747
theorem mstep11 : Lmstep11 = Mmstep11 := by
  have hL : Lmstep11.natDegree ≤ 18 := by unfold Lmstep11; compute_degree!
  have hR : Mmstep11.natDegree ≤ 18 := by unfold Mmstep11; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep11, Mmstep11, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep12 : (ZMod 1249)[X] := 673 + X * 81 + X ^ 2 * 255 + X ^ 3 * 1082 + X ^ 4 * 1241 + X ^ 5 * 574 + X ^ 6 * 403 + X ^ 7 * 325 + X ^ 8 * 696 + X ^ 9 * 574 + X ^ 10 * 1153 + X ^ 11 * 505 + X ^ 12 * 239 + X ^ 13 * 404 + X ^ 14 * 712 + X ^ 15 * 607 + X ^ 16 * 1143 + X ^ 17 * 152 + X ^ 18 * 968
def Mmstep12 : (ZMod 1249)[X] := 673 + X * 81 + X ^ 2 * 255 + X ^ 3 * 1082 + X ^ 4 * 1241 + X ^ 5 * 574 + X ^ 6 * 403 + X ^ 7 * 325 + X ^ 8 * 696 + X ^ 9 * 574 + X ^ 10 * 1153 + X ^ 11 * 505 + X ^ 12 * 239 + X ^ 13 * 404 + X ^ 14 * 712 + X ^ 15 * 607 + X ^ 16 * 1143 + X ^ 17 * 152 + X ^ 18 * 968
theorem mstep12 : Lmstep12 = Mmstep12 := by
  have hL : Lmstep12.natDegree ≤ 18 := by unfold Lmstep12; compute_degree!
  have hR : Mmstep12.natDegree ≤ 18 := by unfold Mmstep12; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep12, Mmstep12, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep13 : (ZMod 1249)[X] := 38 + X * 438 + X ^ 2 * 1220 + X ^ 3 * 375 + X ^ 4 * 1022 + X ^ 5 * 426 + X ^ 6 * 46 + X ^ 7 * 1224 + X ^ 8 * 801 + X ^ 9 * 46 + X ^ 10 * 1171 + X ^ 11 * 953 + X ^ 12 * 1119 + X ^ 13 * 1088 + X ^ 14 * 703 + X ^ 15 * 185 + X ^ 16 * 660 + X ^ 17 * 80 + X ^ 18 * 248
def Mmstep13 : (ZMod 1249)[X] := 38 + X * 438 + X ^ 2 * 1220 + X ^ 3 * 375 + X ^ 4 * 1022 + X ^ 5 * 426 + X ^ 6 * 46 + X ^ 7 * 1224 + X ^ 8 * 801 + X ^ 9 * 46 + X ^ 10 * 1171 + X ^ 11 * 953 + X ^ 12 * 1119 + X ^ 13 * 1088 + X ^ 14 * 703 + X ^ 15 * 185 + X ^ 16 * 660 + X ^ 17 * 80 + X ^ 18 * 248
theorem mstep13 : Lmstep13 = Mmstep13 := by
  have hL : Lmstep13.natDegree ≤ 18 := by unfold Lmstep13; compute_degree!
  have hR : Mmstep13.natDegree ≤ 18 := by unfold Mmstep13; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep13, Mmstep13, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep14 : (ZMod 1249)[X] := 1099 + X * 906 + X ^ 2 * 266 + X ^ 3 * 816 + X ^ 4 * 424 + X ^ 5 * 116 + X ^ 6 * 996 + X ^ 7 * 28 + X ^ 8 * 968 + X ^ 9 * 840 + X ^ 10 * 437 + X ^ 11 * 1198 + X ^ 12 * 750 + X ^ 13 * 930 + X ^ 14 * 734 + X ^ 15 * 1216 + X ^ 16 * 409 + X ^ 17 * 691 + X ^ 18 * 826
def Mmstep14 : (ZMod 1249)[X] := 1099 + X * 906 + X ^ 2 * 266 + X ^ 3 * 816 + X ^ 4 * 424 + X ^ 5 * 116 + X ^ 6 * 996 + X ^ 7 * 28 + X ^ 8 * 968 + X ^ 9 * 840 + X ^ 10 * 437 + X ^ 11 * 1198 + X ^ 12 * 750 + X ^ 13 * 930 + X ^ 14 * 734 + X ^ 15 * 1216 + X ^ 16 * 409 + X ^ 17 * 691 + X ^ 18 * 826
theorem mstep14 : Lmstep14 = Mmstep14 := by
  have hL : Lmstep14.natDegree ≤ 18 := by unfold Lmstep14; compute_degree!
  have hR : Mmstep14.natDegree ≤ 18 := by unfold Mmstep14; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep14, Mmstep14, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep15 : (ZMod 1249)[X] := 159 + X * 109 + X ^ 2 * 1213 + X ^ 3 * 1153 + X ^ 4 * 1071 + X ^ 5 * 297 + X ^ 6 * 196 + X ^ 7 * 984 + X ^ 8 * 85 + X ^ 9 * 843 + X ^ 10 * 1092 + X ^ 11 * 532 + X ^ 12 * 866 + X ^ 13 * 285 + X ^ 14 * 128 + X ^ 15 * 1200 + X ^ 16 * 290 + X ^ 17 * 936 + X ^ 18 * 135
def Mmstep15 : (ZMod 1249)[X] := 159 + X * 109 + X ^ 2 * 1213 + X ^ 3 * 1153 + X ^ 4 * 1071 + X ^ 5 * 297 + X ^ 6 * 196 + X ^ 7 * 984 + X ^ 8 * 85 + X ^ 9 * 843 + X ^ 10 * 1092 + X ^ 11 * 532 + X ^ 12 * 866 + X ^ 13 * 285 + X ^ 14 * 128 + X ^ 15 * 1200 + X ^ 16 * 290 + X ^ 17 * 936 + X ^ 18 * 135
theorem mstep15 : Lmstep15 = Mmstep15 := by
  have hL : Lmstep15.natDegree ≤ 18 := by unfold Lmstep15; compute_degree!
  have hR : Mmstep15.natDegree ≤ 18 := by unfold Mmstep15; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep15, Mmstep15, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep16 : (ZMod 1249)[X] := 55 + X * 407 + X ^ 2 * 650 + X ^ 3 * 790 + X ^ 4 * 712 + X ^ 5 * 638 + X ^ 6 * 332 + X ^ 7 * 913 + X ^ 8 * 865 + X ^ 9 * 300 + X ^ 10 * 547 + X ^ 11 * 1212 + X ^ 12 * 543 + X ^ 13 * 350 + X ^ 14 * 142 + X ^ 15 * 388 + X ^ 16 * 101 + X ^ 17 * 129 + X ^ 18 * 392
def Mmstep16 : (ZMod 1249)[X] := 55 + X * 407 + X ^ 2 * 650 + X ^ 3 * 790 + X ^ 4 * 712 + X ^ 5 * 638 + X ^ 6 * 332 + X ^ 7 * 913 + X ^ 8 * 865 + X ^ 9 * 300 + X ^ 10 * 547 + X ^ 11 * 1212 + X ^ 12 * 543 + X ^ 13 * 350 + X ^ 14 * 142 + X ^ 15 * 388 + X ^ 16 * 101 + X ^ 17 * 129 + X ^ 18 * 392
theorem mstep16 : Lmstep16 = Mmstep16 := by
  have hL : Lmstep16.natDegree ≤ 18 := by unfold Lmstep16; compute_degree!
  have hR : Mmstep16.natDegree ≤ 18 := by unfold Mmstep16; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep16, Mmstep16, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep17 : (ZMod 1249)[X] := 1220 + X * 482 + X ^ 2 * 292 + X ^ 3 * 936 + X ^ 4 * 239 + X ^ 5 * 886 + X ^ 6 * 865 + X ^ 7 * 530 + X ^ 8 * 382 + X ^ 9 * 463 + X ^ 10 * 571 + X ^ 11 * 713 + X ^ 12 * 123 + X ^ 13 * 1148 + X ^ 14 * 779 + X ^ 15 * 1087 + X ^ 16 * 812 + X ^ 17 * 783 + X ^ 18 * 661
def Mmstep17 : (ZMod 1249)[X] := 1220 + X * 482 + X ^ 2 * 292 + X ^ 3 * 936 + X ^ 4 * 239 + X ^ 5 * 886 + X ^ 6 * 865 + X ^ 7 * 530 + X ^ 8 * 382 + X ^ 9 * 463 + X ^ 10 * 571 + X ^ 11 * 713 + X ^ 12 * 123 + X ^ 13 * 1148 + X ^ 14 * 779 + X ^ 15 * 1087 + X ^ 16 * 812 + X ^ 17 * 783 + X ^ 18 * 661
theorem mstep17 : Lmstep17 = Mmstep17 := by
  have hL : Lmstep17.natDegree ≤ 18 := by unfold Lmstep17; compute_degree!
  have hR : Mmstep17.natDegree ≤ 18 := by unfold Mmstep17; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep17, Mmstep17, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep18 : (ZMod 1249)[X] := 542 + X * 695 + X ^ 2 * 13 + X ^ 3 * 449 + X ^ 4 * 862 + X ^ 5 * 585 + X ^ 6 * 93 + X ^ 7 * 381 + X ^ 8 * 843 + X ^ 9 * 367 + X ^ 10 * 340 + X ^ 11 * 854 + X ^ 12 * 793 + X ^ 13 * 769 + X ^ 14 * 543 + X ^ 15 * 865 + X ^ 16 * 426 + X ^ 17 * 75 + X ^ 18 * 357
def Mmstep18 : (ZMod 1249)[X] := 542 + X * 695 + X ^ 2 * 13 + X ^ 3 * 449 + X ^ 4 * 862 + X ^ 5 * 585 + X ^ 6 * 93 + X ^ 7 * 381 + X ^ 8 * 843 + X ^ 9 * 367 + X ^ 10 * 340 + X ^ 11 * 854 + X ^ 12 * 793 + X ^ 13 * 769 + X ^ 14 * 543 + X ^ 15 * 865 + X ^ 16 * 426 + X ^ 17 * 75 + X ^ 18 * 357
theorem mstep18 : Lmstep18 = Mmstep18 := by
  have hL : Lmstep18.natDegree ≤ 18 := by unfold Lmstep18; compute_degree!
  have hR : Mmstep18.natDegree ≤ 18 := by unfold Mmstep18; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep18, Mmstep18, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep19 : (ZMod 1249)[X] := 319 + X * 127 + X ^ 2 * 740 + X ^ 3 * 91 + X ^ 4 * 239 + X ^ 6 * 694 + X ^ 7 * 551 + X ^ 8 * 66 + X ^ 9 * 179 + X ^ 10 * 1037 + X ^ 11 * 114 + X ^ 12 * 349 + X ^ 13 * 135 + X ^ 14 * 448 + X ^ 15 * 1202 + X ^ 16 * 313 + X ^ 17 * 981 + X ^ 18 * 815
def Mmstep19 : (ZMod 1249)[X] := 319 + X * 127 + X ^ 2 * 740 + X ^ 3 * 91 + X ^ 4 * 239 + X ^ 6 * 694 + X ^ 7 * 551 + X ^ 8 * 66 + X ^ 9 * 179 + X ^ 10 * 1037 + X ^ 11 * 114 + X ^ 12 * 349 + X ^ 13 * 135 + X ^ 14 * 448 + X ^ 15 * 1202 + X ^ 16 * 313 + X ^ 17 * 981 + X ^ 18 * 815
theorem mstep19 : Lmstep19 = Mmstep19 := by
  have hL : Lmstep19.natDegree ≤ 18 := by unfold Lmstep19; compute_degree!
  have hR : Mmstep19.natDegree ≤ 18 := by unfold Mmstep19; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep19, Mmstep19, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep20 : (ZMod 1249)[X] := 954 + X * 247 + X ^ 2 * 745 + X ^ 3 * 463 + X ^ 4 * 705 + X ^ 5 * 585 + X ^ 6 * 930 + X ^ 7 * 1036 + X ^ 8 * 798 + X ^ 9 * 1117 + X ^ 10 * 1073 + X ^ 11 * 883 + X ^ 12 * 570 + X ^ 13 * 31 + X ^ 14 * 517 + X ^ 15 * 435 + X ^ 16 * 817 + X ^ 17 * 557 + X ^ 18 * 95
def Mmstep20 : (ZMod 1249)[X] := 954 + X * 247 + X ^ 2 * 745 + X ^ 3 * 463 + X ^ 4 * 705 + X ^ 5 * 585 + X ^ 6 * 930 + X ^ 7 * 1036 + X ^ 8 * 798 + X ^ 9 * 1117 + X ^ 10 * 1073 + X ^ 11 * 883 + X ^ 12 * 570 + X ^ 13 * 31 + X ^ 14 * 517 + X ^ 15 * 435 + X ^ 16 * 817 + X ^ 17 * 557 + X ^ 18 * 95
theorem mstep20 : Lmstep20 = Mmstep20 := by
  have hL : Lmstep20.natDegree ≤ 18 := by unfold Lmstep20; compute_degree!
  have hR : Mmstep20.natDegree ≤ 18 := by unfold Mmstep20; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep20, Mmstep20, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lmstep21 : (ZMod 1249)[X] := 399 + X * 1024 + X ^ 2 * 1034 + X ^ 3 * 629 + X ^ 4 * 580 + X ^ 5 * 1090 + X ^ 6 * 22 + X ^ 7 * 784 + X ^ 8 * 355 + X ^ 9 * 949 + X ^ 10 * 1176 + X ^ 11 * 781 + X ^ 12 * 71 + X ^ 13 * 1172 + X ^ 14 * 894 + X ^ 15 * 557 + X ^ 16 * 623 + X ^ 17 * 931 + X ^ 18 * 821
def Mmstep21 : (ZMod 1249)[X] := 399 + X * 1024 + X ^ 2 * 1034 + X ^ 3 * 629 + X ^ 4 * 580 + X ^ 5 * 1090 + X ^ 6 * 22 + X ^ 7 * 784 + X ^ 8 * 355 + X ^ 9 * 949 + X ^ 10 * 1176 + X ^ 11 * 781 + X ^ 12 * 71 + X ^ 13 * 1172 + X ^ 14 * 894 + X ^ 15 * 557 + X ^ 16 * 623 + X ^ 17 * 931 + X ^ 18 * 821
theorem mstep21 : Lmstep21 = Mmstep21 := by
  have hL : Lmstep21.natDegree ≤ 18 := by unfold Lmstep21; compute_degree!
  have hR : Mmstep21.natDegree ≤ 18 := by unfold Mmstep21; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lmstep21, Mmstep21, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2568Batch9Actual

end