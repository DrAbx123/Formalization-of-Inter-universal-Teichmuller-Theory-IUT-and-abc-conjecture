import tmp.sheaf.xif.paper.S2566Batch7Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2566Batch7Actual

namespace LeanFormal.IUT.XiFPaper.S2567Batch8Actual

def H0 : (ZMod 1249)[X] := 934 + X * 1084 + X ^ 2 * 365 + X ^ 3 * 289 + X ^ 4 * 720 + X ^ 5 * 235 + X ^ 6 * 880 + X ^ 7 * 176 + X ^ 8 * 1017 + X ^ 9 * 428
def H1 : (ZMod 1249)[X] := 1213 + X * 833 + X ^ 2 * 1024 + X ^ 3 * 1188 + X ^ 4 * 577 + X ^ 5 * 401 + X ^ 6 * 837 + X ^ 7 * 598 + X ^ 8 * 282 + X ^ 9 * 345
def H2 : (ZMod 1249)[X] := 27 + X * 576 + X ^ 2 * 708 + X ^ 3 * 274 + X ^ 4 * 863 + X ^ 5 * 912 + X ^ 6 * 37 + X ^ 7 * 1146 + X ^ 8 * 792 + X ^ 9 * 603
def H3 : (ZMod 1249)[X] := 939 + X * 1204 + X ^ 2 * 269 + X ^ 3 * 464 + X ^ 4 * 719 + X ^ 5 * 528 + X ^ 6 * 878 + X ^ 7 * 797 + X ^ 8 * 460 + X ^ 9 * 696
def H4 : (ZMod 1249)[X] := 418 + X * 514 + X ^ 2 * 36 + X ^ 3 * 1064 + X ^ 4 * 444 + X ^ 5 * 813 + X ^ 6 * 1204 + X ^ 7 * 427 + X ^ 8 * 756 + X ^ 9 * 324
def H5 : (ZMod 1249)[X] := 585 + X * 265 + X ^ 2 * 693 + X ^ 3 * 744 + X ^ 4 * 724 + X ^ 5 * 209 + X ^ 6 * 947 + X ^ 7 * 976 + X ^ 8 * 22 + X ^ 9 * 481
def H6 : (ZMod 1249)[X] := 77 + X * 449 + X ^ 2 * 475 + X ^ 3 * 332 + X ^ 4 * 1068 + X ^ 5 * 1027 + X ^ 6 * 1235 + X ^ 7 * 511 + X ^ 8 * 280 + X ^ 9 * 761
def H7 : (ZMod 1249)[X] := 1137 + X * 265 + X ^ 2 * 270 + X ^ 3 * 966 + X ^ 4 * 853 + X ^ 5 * 865 + X ^ 6 * 967 + X ^ 7 * 26 + X ^ 8 * 984 + X ^ 9 * 570
def H8 : (ZMod 1249)[X] := 1207 + X * 846 + X ^ 2 * 1003 + X ^ 3 * 562 + X ^ 4 * 318 + X ^ 5 * 972 + X ^ 6 * 146 + X ^ 7 * 555 + X ^ 8 * 1101 + X ^ 9 * 997
def H9 : (ZMod 1249)[X] := 250 + X * 119 + X ^ 2 * 429 + X ^ 3 * 441 + X ^ 4 * 974 + X ^ 5 * 1004 + X ^ 6 * 625 + X ^ 7 * 351 + X ^ 8 * 4 + X ^ 9 * 471
def H10 : (ZMod 1249)[X] := 523 + X * 694 + X ^ 2 * 1179 + X ^ 3 * 193 + X ^ 4 * 1132 + X ^ 5 * 246 + X ^ 6 * 599 + X ^ 7 * 297 + X ^ 8 * 751 + X ^ 9 * 377
def H11 : (ZMod 1249)[X] := 1201 + X * 260 + X ^ 2 * 1018 + X ^ 3 * 1111 + X ^ 4 * 67 + X ^ 5 * 125 + X ^ 6 * 984 + X ^ 7 * 93 + X ^ 8 * 761 + X ^ 9 * 922
def H12 : (ZMod 1249)[X] := 770 + X * 832 + X ^ 2 * 798 + X ^ 3 * 1159 + X ^ 4 * 843 + X ^ 5 * 1143 + X ^ 6 * 215 + X ^ 7 * 164 + X ^ 8 * 767 + X ^ 9 * 56
def H13 : (ZMod 1249)[X] := 72 + X * 263 + X ^ 2 * 1063 + X ^ 3 * 802 + X ^ 4 * 665 + X ^ 5 * 586 + X ^ 6 * 1067 + X ^ 7 * 745 + X ^ 8 * 704 + X ^ 9 * 345
def H14 : (ZMod 1249)[X] := 157 + X * 332 + X ^ 2 * 275 + X ^ 3 * 860 + X ^ 4 * 551 + X ^ 5 * 621 + X ^ 6 * 465 + X ^ 7 * 436 + X ^ 8 * 515 + X ^ 9 * 1233
def H15 : (ZMod 1249)[X] := 1155 + X * 15 + X ^ 2 * 569 + X ^ 3 * 702 + X ^ 4 * 1130 + X ^ 5 * 609 + X ^ 6 * 82 + X ^ 7 * 200 + X ^ 8 * 1197 + X ^ 9 * 990
def Lhstep0 : (ZMod 1249)[X] := 554 + X * 283 + X ^ 2 * 862 + X ^ 3 * 987 + X ^ 4 * 172 + X ^ 5 * 180 + X ^ 6 * 902 + X ^ 7 * 329 + X ^ 8 * 818 + X ^ 9 * 566 + X ^ 10 * 694 + X ^ 11 * 1060 + X ^ 12 * 1040 + X ^ 13 * 194 + X ^ 14 * 1174 + X ^ 15 * 903 + X ^ 16 * 893 + X ^ 17 * 1248 + X ^ 18 * 830
def Mhstep0 : (ZMod 1249)[X] := 554 + X * 283 + X ^ 2 * 862 + X ^ 3 * 987 + X ^ 4 * 172 + X ^ 5 * 180 + X ^ 6 * 902 + X ^ 7 * 329 + X ^ 8 * 818 + X ^ 9 * 566 + X ^ 10 * 694 + X ^ 11 * 1060 + X ^ 12 * 1040 + X ^ 13 * 194 + X ^ 14 * 1174 + X ^ 15 * 903 + X ^ 16 * 893 + X ^ 17 * 1248 + X ^ 18 * 830
theorem hstep0 : Lhstep0 = Mhstep0 := by
  have hL : Lhstep0.natDegree ≤ 18 := by unfold Lhstep0; compute_degree!
  have hR : Mhstep0.natDegree ≤ 18 := by unfold Mhstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep0, Mhstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep1 : (ZMod 1249)[X] := 47 + X * 1225 + X ^ 2 * 657 + X ^ 3 * 495 + X ^ 4 * 1130 + X ^ 5 * 628 + X ^ 6 * 904 + X ^ 7 * 173 + X ^ 8 * 278 + X ^ 9 * 691 + X ^ 10 * 315 + X ^ 11 * 150 + X ^ 12 * 924 + X ^ 13 * 397 + X ^ 14 * 997 + X ^ 15 * 534 + X ^ 16 * 38 + X ^ 17 * 985 + X ^ 18 * 370
def Mhstep1 : (ZMod 1249)[X] := 47 + X * 1225 + X ^ 2 * 657 + X ^ 3 * 495 + X ^ 4 * 1130 + X ^ 5 * 628 + X ^ 6 * 904 + X ^ 7 * 173 + X ^ 8 * 278 + X ^ 9 * 691 + X ^ 10 * 315 + X ^ 11 * 150 + X ^ 12 * 924 + X ^ 13 * 397 + X ^ 14 * 997 + X ^ 15 * 534 + X ^ 16 * 38 + X ^ 17 * 985 + X ^ 18 * 370
theorem hstep1 : Lhstep1 = Mhstep1 := by
  have hL : Lhstep1.natDegree ≤ 18 := by unfold Lhstep1; compute_degree!
  have hR : Mhstep1.natDegree ≤ 18 := by unfold Mhstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep1, Mhstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep2 : (ZMod 1249)[X] := 729 + X * 1128 + X ^ 2 * 304 + X ^ 3 * 1076 + X ^ 4 * 455 + X ^ 5 * 54 + X ^ 6 * 337 + X ^ 7 * 320 + X ^ 8 * 776 + X ^ 9 * 402 + X ^ 10 * 1165 + X ^ 11 * 1016 + X ^ 12 * 892 + X ^ 13 * 997 + X ^ 14 * 25 + X ^ 15 * 125 + X ^ 16 * 948 + X ^ 17 * 916 + X ^ 18 * 150
def Mhstep2 : (ZMod 1249)[X] := 729 + X * 1128 + X ^ 2 * 304 + X ^ 3 * 1076 + X ^ 4 * 455 + X ^ 5 * 54 + X ^ 6 * 337 + X ^ 7 * 320 + X ^ 8 * 776 + X ^ 9 * 402 + X ^ 10 * 1165 + X ^ 11 * 1016 + X ^ 12 * 892 + X ^ 13 * 997 + X ^ 14 * 25 + X ^ 15 * 125 + X ^ 16 * 948 + X ^ 17 * 916 + X ^ 18 * 150
theorem hstep2 : Lhstep2 = Mhstep2 := by
  have hL : Lhstep2.natDegree ≤ 18 := by unfold Lhstep2; compute_degree!
  have hR : Mhstep2.natDegree ≤ 18 := by unfold Mhstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep2, Mhstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep3 : (ZMod 1249)[X] := 1176 + X * 422 + X ^ 2 * 113 + X ^ 3 * 360 + X ^ 4 * 738 + X ^ 5 * 1197 + X ^ 6 * 246 + X ^ 7 * 938 + X ^ 8 * 777 + X ^ 9 * 1138 + X ^ 10 * 278 + X ^ 11 * 633 + X ^ 12 * 971 + X ^ 13 * 950 + X ^ 14 * 938 + X ^ 15 * 731 + X ^ 16 * 831 + X ^ 17 * 832 + X ^ 18 * 1053
def Mhstep3 : (ZMod 1249)[X] := 1176 + X * 422 + X ^ 2 * 113 + X ^ 3 * 360 + X ^ 4 * 738 + X ^ 5 * 1197 + X ^ 6 * 246 + X ^ 7 * 938 + X ^ 8 * 777 + X ^ 9 * 1138 + X ^ 10 * 278 + X ^ 11 * 633 + X ^ 12 * 971 + X ^ 13 * 950 + X ^ 14 * 938 + X ^ 15 * 731 + X ^ 16 * 831 + X ^ 17 * 832 + X ^ 18 * 1053
theorem hstep3 : Lhstep3 = Mhstep3 := by
  have hL : Lhstep3.natDegree ≤ 18 := by unfold Lhstep3; compute_degree!
  have hR : Mhstep3.natDegree ≤ 18 := by unfold Mhstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep3, Mhstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep4 : (ZMod 1249)[X] := 1113 + X * 48 + X ^ 2 * 777 + X ^ 3 * 1003 + X ^ 4 * 1195 + X ^ 5 * 1178 + X ^ 6 * 29 + X ^ 7 * 132 + X ^ 8 * 1079 + X ^ 9 * 75 + X ^ 10 * 1203 + X ^ 11 * 903 + X ^ 12 * 24 + X ^ 13 * 971 + X ^ 14 * 376 + X ^ 15 * 707 + X ^ 16 * 161 + X ^ 17 * 280 + X ^ 18 * 60
def Mhstep4 : (ZMod 1249)[X] := 1113 + X * 48 + X ^ 2 * 777 + X ^ 3 * 1003 + X ^ 4 * 1195 + X ^ 5 * 1178 + X ^ 6 * 29 + X ^ 7 * 132 + X ^ 8 * 1079 + X ^ 9 * 75 + X ^ 10 * 1203 + X ^ 11 * 903 + X ^ 12 * 24 + X ^ 13 * 971 + X ^ 14 * 376 + X ^ 15 * 707 + X ^ 16 * 161 + X ^ 17 * 280 + X ^ 18 * 60
theorem hstep4 : Lhstep4 = Mhstep4 := by
  have hL : Lhstep4.natDegree ≤ 18 := by unfold Lhstep4; compute_degree!
  have hR : Mhstep4.natDegree ≤ 18 := by unfold Mhstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep4, Mhstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep5 : (ZMod 1249)[X] := 1248 + X * 298 + X ^ 2 * 490 + X ^ 3 * 11 + X ^ 4 * 527 + X ^ 5 * 762 + X ^ 6 * 482 + X ^ 7 * 726 + X ^ 8 * 384 + X ^ 9 * 597 + X ^ 10 * 171 + X ^ 11 * 504 + X ^ 12 * 254 + X ^ 13 * 23 + X ^ 14 * 9 + X ^ 15 * 971 + X ^ 16 * 148 + X ^ 17 * 1180 + X ^ 18 * 296
def Mhstep5 : (ZMod 1249)[X] := 1248 + X * 298 + X ^ 2 * 490 + X ^ 3 * 11 + X ^ 4 * 527 + X ^ 5 * 762 + X ^ 6 * 482 + X ^ 7 * 726 + X ^ 8 * 384 + X ^ 9 * 597 + X ^ 10 * 171 + X ^ 11 * 504 + X ^ 12 * 254 + X ^ 13 * 23 + X ^ 14 * 9 + X ^ 15 * 971 + X ^ 16 * 148 + X ^ 17 * 1180 + X ^ 18 * 296
theorem hstep5 : Lhstep5 = Mhstep5 := by
  have hL : Lhstep5.natDegree ≤ 18 := by unfold Lhstep5; compute_degree!
  have hR : Mhstep5.natDegree ≤ 18 := by unfold Mhstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep5, Mhstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep6 : (ZMod 1249)[X] := 933 + X * 451 + X ^ 2 * 1220 + X ^ 3 * 560 + X ^ 4 * 34 + X ^ 5 * 19 + X ^ 6 * 301 + X ^ 7 * 1075 + X ^ 8 * 600 + X ^ 9 * 892 + X ^ 10 * 359 + X ^ 11 * 688 + X ^ 12 * 1147 + X ^ 13 * 558 + X ^ 14 * 329 + X ^ 15 * 64 + X ^ 16 * 577 + X ^ 17 * 251 + X ^ 18 * 834
def Mhstep6 : (ZMod 1249)[X] := 933 + X * 451 + X ^ 2 * 1220 + X ^ 3 * 560 + X ^ 4 * 34 + X ^ 5 * 19 + X ^ 6 * 301 + X ^ 7 * 1075 + X ^ 8 * 600 + X ^ 9 * 892 + X ^ 10 * 359 + X ^ 11 * 688 + X ^ 12 * 1147 + X ^ 13 * 558 + X ^ 14 * 329 + X ^ 15 * 64 + X ^ 16 * 577 + X ^ 17 * 251 + X ^ 18 * 834
theorem hstep6 : Lhstep6 = Mhstep6 := by
  have hL : Lhstep6.natDegree ≤ 18 := by unfold Lhstep6; compute_degree!
  have hR : Mhstep6.natDegree ≤ 18 := by unfold Mhstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep6, Mhstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep7 : (ZMod 1249)[X] := 54 + X * 592 + X ^ 2 * 1002 + X ^ 3 * 407 + X ^ 4 * 373 + X ^ 5 * 594 + X ^ 6 * 677 + X ^ 7 * 131 + X ^ 8 * 256 + X ^ 9 * 1067 + X ^ 10 * 496 + X ^ 11 * 547 + X ^ 12 * 523 + X ^ 13 * 955 + X ^ 14 * 895 + X ^ 15 * 721 + X ^ 16 * 1194 + X ^ 17 * 158 + X ^ 18 * 160
def Mhstep7 : (ZMod 1249)[X] := 54 + X * 592 + X ^ 2 * 1002 + X ^ 3 * 407 + X ^ 4 * 373 + X ^ 5 * 594 + X ^ 6 * 677 + X ^ 7 * 131 + X ^ 8 * 256 + X ^ 9 * 1067 + X ^ 10 * 496 + X ^ 11 * 547 + X ^ 12 * 523 + X ^ 13 * 955 + X ^ 14 * 895 + X ^ 15 * 721 + X ^ 16 * 1194 + X ^ 17 * 158 + X ^ 18 * 160
theorem hstep7 : Lhstep7 = Mhstep7 := by
  have hL : Lhstep7.natDegree ≤ 18 := by unfold Lhstep7; compute_degree!
  have hR : Mhstep7.natDegree ≤ 18 := by unfold Mhstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep7, Mhstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep8 : (ZMod 1249)[X] := 515 + X * 129 + X ^ 2 * 719 + X ^ 3 * 1188 + X ^ 4 * 496 + X ^ 5 * 48 + X ^ 6 * 682 + X ^ 7 * 933 + X ^ 8 * 1221 + X ^ 9 * 212 + X ^ 10 * 189 + X ^ 11 * 1161 + X ^ 12 * 938 + X ^ 13 * 97 + X ^ 14 * 990 + X ^ 15 * 695 + X ^ 16 * 727 + X ^ 17 * 901 + X ^ 18 * 1054
def Mhstep8 : (ZMod 1249)[X] := 515 + X * 129 + X ^ 2 * 719 + X ^ 3 * 1188 + X ^ 4 * 496 + X ^ 5 * 48 + X ^ 6 * 682 + X ^ 7 * 933 + X ^ 8 * 1221 + X ^ 9 * 212 + X ^ 10 * 189 + X ^ 11 * 1161 + X ^ 12 * 938 + X ^ 13 * 97 + X ^ 14 * 990 + X ^ 15 * 695 + X ^ 16 * 727 + X ^ 17 * 901 + X ^ 18 * 1054
theorem hstep8 : Lhstep8 = Mhstep8 := by
  have hL : Lhstep8.natDegree ≤ 18 := by unfold Lhstep8; compute_degree!
  have hR : Mhstep8.natDegree ≤ 18 := by unfold Mhstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep8, Mhstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep9 : (ZMod 1249)[X] := 50 + X * 797 + X ^ 2 * 94 + X ^ 3 * 360 + X ^ 4 * 370 + X ^ 5 * 580 + X ^ 6 * 391 + X ^ 7 * 137 + X ^ 8 * 458 + X ^ 9 * 839 + X ^ 10 * 250 + X ^ 11 * 772 + X ^ 12 * 1112 + X ^ 13 * 382 + X ^ 14 * 1078 + X ^ 15 * 781 + X ^ 16 * 922 + X ^ 17 * 21 + X ^ 18 * 768
def Mhstep9 : (ZMod 1249)[X] := 50 + X * 797 + X ^ 2 * 94 + X ^ 3 * 360 + X ^ 4 * 370 + X ^ 5 * 580 + X ^ 6 * 391 + X ^ 7 * 137 + X ^ 8 * 458 + X ^ 9 * 839 + X ^ 10 * 250 + X ^ 11 * 772 + X ^ 12 * 1112 + X ^ 13 * 382 + X ^ 14 * 1078 + X ^ 15 * 781 + X ^ 16 * 922 + X ^ 17 * 21 + X ^ 18 * 768
theorem hstep9 : Lhstep9 = Mhstep9 := by
  have hL : Lhstep9.natDegree ≤ 18 := by unfold Lhstep9; compute_degree!
  have hR : Mhstep9.natDegree ≤ 18 := by unfold Mhstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep9, Mhstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep10 : (ZMod 1249)[X] := 1247 + X * 255 + X ^ 2 * 1242 + X ^ 3 * 1051 + X ^ 4 * 522 + X ^ 5 * 454 + X ^ 6 * 1198 + X ^ 7 * 822 + X ^ 8 * 1045 + X ^ 9 * 56 + X ^ 10 * 990 + X ^ 11 * 186 + X ^ 12 * 93 + X ^ 13 * 90 + X ^ 14 * 580 + X ^ 15 * 958 + X ^ 16 * 1069 + X ^ 17 * 457 + X ^ 18 * 992
def Mhstep10 : (ZMod 1249)[X] := 1247 + X * 255 + X ^ 2 * 1242 + X ^ 3 * 1051 + X ^ 4 * 522 + X ^ 5 * 454 + X ^ 6 * 1198 + X ^ 7 * 822 + X ^ 8 * 1045 + X ^ 9 * 56 + X ^ 10 * 990 + X ^ 11 * 186 + X ^ 12 * 93 + X ^ 13 * 90 + X ^ 14 * 580 + X ^ 15 * 958 + X ^ 16 * 1069 + X ^ 17 * 457 + X ^ 18 * 992
theorem hstep10 : Lhstep10 = Mhstep10 := by
  have hL : Lhstep10.natDegree ≤ 18 := by unfold Lhstep10; compute_degree!
  have hR : Mhstep10.natDegree ≤ 18 := by unfold Mhstep10; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep10, Mhstep10, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep11 : (ZMod 1249)[X] := 1055 + X * 20 + X ^ 2 * 1097 + X ^ 3 * 542 + X ^ 4 * 149 + X ^ 5 * 415 + X ^ 6 * 1092 + X ^ 7 * 601 + X ^ 8 * 277 + X ^ 9 * 665 + X ^ 10 * 1120 + X ^ 11 * 909 + X ^ 12 * 929 + X ^ 13 * 969 + X ^ 14 * 687 + X ^ 15 * 108 + X ^ 16 * 1213 + X ^ 17 * 657 + X ^ 18 * 764
def Mhstep11 : (ZMod 1249)[X] := 1055 + X * 20 + X ^ 2 * 1097 + X ^ 3 * 542 + X ^ 4 * 149 + X ^ 5 * 415 + X ^ 6 * 1092 + X ^ 7 * 601 + X ^ 8 * 277 + X ^ 9 * 665 + X ^ 10 * 1120 + X ^ 11 * 909 + X ^ 12 * 929 + X ^ 13 * 969 + X ^ 14 * 687 + X ^ 15 * 108 + X ^ 16 * 1213 + X ^ 17 * 657 + X ^ 18 * 764
theorem hstep11 : Lhstep11 = Mhstep11 := by
  have hL : Lhstep11.natDegree ≤ 18 := by unfold Lhstep11; compute_degree!
  have hR : Mhstep11.natDegree ≤ 18 := by unfold Mhstep11; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep11, Mhstep11, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep12 : (ZMod 1249)[X] := 874 + X * 1055 + X ^ 2 * 182 + X ^ 3 * 224 + X ^ 4 * 443 + X ^ 5 * 499 + X ^ 6 * 701 + X ^ 7 * 885 + X ^ 8 * 218 + X ^ 9 * 482 + X ^ 10 * 352 + X ^ 11 * 1135 + X ^ 12 * 575 + X ^ 13 * 1083 + X ^ 14 * 110 + X ^ 15 * 876 + X ^ 16 * 892 + X ^ 17 * 972 + X ^ 18 * 638
def Mhstep12 : (ZMod 1249)[X] := 874 + X * 1055 + X ^ 2 * 182 + X ^ 3 * 224 + X ^ 4 * 443 + X ^ 5 * 499 + X ^ 6 * 701 + X ^ 7 * 885 + X ^ 8 * 218 + X ^ 9 * 482 + X ^ 10 * 352 + X ^ 11 * 1135 + X ^ 12 * 575 + X ^ 13 * 1083 + X ^ 14 * 110 + X ^ 15 * 876 + X ^ 16 * 892 + X ^ 17 * 972 + X ^ 18 * 638
theorem hstep12 : Lhstep12 = Mhstep12 := by
  have hL : Lhstep12.natDegree ≤ 18 := by unfold Lhstep12; compute_degree!
  have hR : Mhstep12.natDegree ≤ 18 := by unfold Mhstep12; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep12, Mhstep12, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep13 : (ZMod 1249)[X] := 188 + X * 402 + X ^ 2 * 1168 + X ^ 3 * 166 + X ^ 4 * 150 + X ^ 5 * 938 + X ^ 6 * 894 + X ^ 7 * 904 + X ^ 8 * 924 + X ^ 9 * 800 + X ^ 10 * 621 + X ^ 11 * 1095 + X ^ 12 * 382 + X ^ 13 * 1068 + X ^ 14 * 1171 + X ^ 15 * 369 + X ^ 16 * 474 + X ^ 17 * 1148 + X ^ 18 * 370
def Mhstep13 : (ZMod 1249)[X] := 188 + X * 402 + X ^ 2 * 1168 + X ^ 3 * 166 + X ^ 4 * 150 + X ^ 5 * 938 + X ^ 6 * 894 + X ^ 7 * 904 + X ^ 8 * 924 + X ^ 9 * 800 + X ^ 10 * 621 + X ^ 11 * 1095 + X ^ 12 * 382 + X ^ 13 * 1068 + X ^ 14 * 1171 + X ^ 15 * 369 + X ^ 16 * 474 + X ^ 17 * 1148 + X ^ 18 * 370
theorem hstep13 : Lhstep13 = Mhstep13 := by
  have hL : Lhstep13.natDegree ≤ 18 := by unfold Lhstep13; compute_degree!
  have hR : Mhstep13.natDegree ≤ 18 := by unfold Mhstep13; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep13, Mhstep13, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lhstep14 : (ZMod 1249)[X] := 918 + X * 581 + X ^ 2 * 481 + X ^ 3 * 502 + X ^ 4 * 335 + X ^ 5 * 935 + X ^ 6 * 1035 + X ^ 7 * 73 + X ^ 8 * 349 + X ^ 9 * 28 + X ^ 10 * 904 + X ^ 11 * 301 + X ^ 12 * 36 + X ^ 13 * 800 + X ^ 14 * 943 + X ^ 15 * 797 + X ^ 16 * 224 + X ^ 17 * 1006 + X ^ 18 * 256
def Mhstep14 : (ZMod 1249)[X] := 918 + X * 581 + X ^ 2 * 481 + X ^ 3 * 502 + X ^ 4 * 335 + X ^ 5 * 935 + X ^ 6 * 1035 + X ^ 7 * 73 + X ^ 8 * 349 + X ^ 9 * 28 + X ^ 10 * 904 + X ^ 11 * 301 + X ^ 12 * 36 + X ^ 13 * 800 + X ^ 14 * 943 + X ^ 15 * 797 + X ^ 16 * 224 + X ^ 17 * 1006 + X ^ 18 * 256
theorem hstep14 : Lhstep14 = Mhstep14 := by
  have hL : Lhstep14.natDegree ≤ 18 := by unfold Lhstep14; compute_degree!
  have hR : Mhstep14.natDegree ≤ 18 := by unfold Mhstep14; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lhstep14, Mhstep14, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2567Batch8Actual

end