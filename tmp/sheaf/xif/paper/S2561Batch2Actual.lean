import tmp.sheaf.xif.paper.S2560Batch1Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1Actual

namespace LeanFormal.IUT.XiFPaper.S2561Batch2Actual

def T0 : (ZMod 1249)[X] := 91 + X * 1214 + X ^ 2 * 319 + X ^ 3 * 805 + X ^ 4 * 483 + X ^ 5 * 435 + X ^ 6 * 1242 + X ^ 7 * 371 + X ^ 8 * 124 + X ^ 9 * 193
def T1 : (ZMod 1249)[X] := 428 + X * 197 + X ^ 2 * 164 + X ^ 3 * 226 + X ^ 4 * 199 + X ^ 5 * 1137 + X ^ 6 * 1163 + X ^ 7 * 780 + X ^ 8 * 1163 + X ^ 9 * 617
def T2 : (ZMod 1249)[X] := 656 + X * 538 + X ^ 2 * 1242 + X ^ 3 * 988 + X ^ 4 * 45 + X ^ 5 * 358 + X ^ 6 * 395 + X ^ 7 * 241 + X ^ 8 * 245 + X ^ 9 * 280
def T3 : (ZMod 1249)[X] := 638 + X * 237 + X ^ 2 * 462 + X ^ 3 * 445 + X ^ 4 * 530 + X ^ 5 * 386 + X ^ 6 * 1217 + X ^ 7 * 766 + X ^ 8 * 682 + X ^ 9 * 825
def T4 : (ZMod 1249)[X] := 1116 + X * 1078 + X ^ 2 * 786 + X ^ 3 * 643 + X ^ 4 * 776 + X ^ 5 * 720 + X ^ 6 * 1083 + X ^ 7 * 988 + X ^ 8 * 1201 + X ^ 9 * 56
def U0 : (ZMod 1249)[X] := 1116 + X * 1078 + X ^ 2 * 786 + X ^ 3 * 643 + X ^ 4 * 776 + X ^ 5 * 720 + X ^ 6 * 1083 + X ^ 7 * 988 + X ^ 8 * 1201 + X ^ 9 * 56
def U1 : (ZMod 1249)[X] := 156 + X * 1212 + X ^ 2 * 1106 + X ^ 3 * 284 + X ^ 4 * 796 + X ^ 5 * 718 + X ^ 6 * 704 + X ^ 7 * 923 + X ^ 8 * 967 + X ^ 9 * 101
def U2 : (ZMod 1249)[X] := 714 + X * 462 + X ^ 2 * 285 + X ^ 3 * 530 + X ^ 4 * 1007 + X ^ 5 * 237 + X ^ 6 * 188 + X ^ 7 * 155 + X ^ 8 * 1112 + X ^ 9 * 701
def U3 : (ZMod 1249)[X] := 584 + X * 1032 + X ^ 2 * 478 + X ^ 3 * 194 + X ^ 4 * 155 + X ^ 5 * 1014 + X ^ 6 * 1239 + X ^ 7 * 1217 + X ^ 8 * 1020 + X ^ 9 * 623
def U4 : (ZMod 1249)[X] := 267 + X * 967 + X ^ 2 * 309 + X ^ 3 * 550 + X ^ 4 * 1179 + X ^ 5 * 612 + X ^ 6 * 578 + X ^ 7 * 1038 + X ^ 8 * 316 + X ^ 9 * 286
def U5 : (ZMod 1249)[X] := 1156 + X * 41 + X ^ 2 * 615 + X ^ 3 * 231 + X ^ 4 * 400 + X ^ 5 * 609 + X ^ 6 * 1080 + X ^ 7 * 791 + X ^ 8 * 1220 + X ^ 9 * 1015
def U6 : (ZMod 1249)[X] := 1173 + X * 570 + X ^ 2 * 176 + X ^ 3 * 825 + X ^ 4 * 1243 + X ^ 5 * 672 + X ^ 6 * 1150 + X ^ 7 * 696 + X ^ 8 * 985 + X ^ 9 * 419
def U7 : (ZMod 1249)[X] := 366 + X * 858 + X ^ 2 * 152 + X ^ 3 * 1007 + X ^ 4 * 685 + X ^ 5 * 421 + X ^ 6 * 74 + X ^ 7 * 523 + X ^ 8 * 568 + X ^ 9 * 954
def U8 : (ZMod 1249)[X] := 432 + X * 972 + X ^ 2 * 137 + X ^ 3 * 956 + X ^ 4 * 339 + X ^ 5 * 518 + X ^ 6 * 380 + X ^ 7 * 648 + X ^ 8 * 112 + X ^ 9 * 834
def U9 : (ZMod 1249)[X] := 555 + X * 872 + X ^ 2 * 144 + X ^ 3 * 685 + X ^ 4 * 1068 + X ^ 5 * 107 + X ^ 6 * 862 + X ^ 7 * 1151 + X ^ 8 * 642 + X ^ 9 * 775
def U10 : (ZMod 1249)[X] := 644 + X * 889 + X ^ 2 * 20 + X ^ 3 * 552 + X ^ 4 * 1015 + X ^ 5 * 1199 + X ^ 6 * 1208 + X ^ 7 * 524 + X ^ 8 * 407 + X ^ 9 * 264
def Ltstep0 : (ZMod 1249)[X] := 1220 + X * 1205 + X ^ 2 * 1059 + X ^ 3 * 718 + X ^ 4 * 467 + X ^ 5 * 434 + X ^ 6 * 1206 + X ^ 7 * 1159 + X ^ 8 * 1145 + X ^ 9 * 514 + X ^ 10 * 617 + X ^ 11 * 80 + X ^ 12 * 622 + X ^ 13 * 953 + X ^ 14 * 390 + X ^ 15 * 1188 + X ^ 16 * 633 + X ^ 17 * 637 + X ^ 18 * 1043
def Mtstep0 : (ZMod 1249)[X] := 1220 + X * 1205 + X ^ 2 * 1059 + X ^ 3 * 718 + X ^ 4 * 467 + X ^ 5 * 434 + X ^ 6 * 1206 + X ^ 7 * 1159 + X ^ 8 * 1145 + X ^ 9 * 514 + X ^ 10 * 617 + X ^ 11 * 80 + X ^ 12 * 622 + X ^ 13 * 953 + X ^ 14 * 390 + X ^ 15 * 1188 + X ^ 16 * 633 + X ^ 17 * 637 + X ^ 18 * 1043
theorem tstep0 : Ltstep0 = Mtstep0 := by
  have hL : Ltstep0.natDegree ≤ 18 := by unfold Ltstep0; compute_degree!
  have hR : Mtstep0.natDegree ≤ 18 := by unfold Mtstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ltstep0, Mtstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ltstep1 : (ZMod 1249)[X] := 784 + X * 560 + X ^ 2 * 37 + X ^ 3 * 264 + X ^ 4 * 670 + X ^ 5 * 100 + X ^ 6 * 1036 + X ^ 7 * 492 + X ^ 8 * 38 + X ^ 9 * 441 + X ^ 10 * 177 + X ^ 11 * 231 + X ^ 12 * 47 + X ^ 13 * 46 + X ^ 14 * 300 + X ^ 15 * 1016 + X ^ 16 * 485 + X ^ 17 * 285 + X ^ 18 * 1208
def Mtstep1 : (ZMod 1249)[X] := 784 + X * 560 + X ^ 2 * 37 + X ^ 3 * 264 + X ^ 4 * 670 + X ^ 5 * 100 + X ^ 6 * 1036 + X ^ 7 * 492 + X ^ 8 * 38 + X ^ 9 * 441 + X ^ 10 * 177 + X ^ 11 * 231 + X ^ 12 * 47 + X ^ 13 * 46 + X ^ 14 * 300 + X ^ 15 * 1016 + X ^ 16 * 485 + X ^ 17 * 285 + X ^ 18 * 1208
theorem tstep1 : Ltstep1 = Mtstep1 := by
  have hL : Ltstep1.natDegree ≤ 18 := by unfold Ltstep1; compute_degree!
  have hR : Mtstep1.natDegree ≤ 18 := by unfold Mtstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ltstep1, Mtstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ltstep2 : (ZMod 1249)[X] := 916 + X * 281 + X ^ 2 * 858 + X ^ 3 * 25 + X ^ 4 * 533 + X ^ 5 * 557 + X ^ 6 * 1041 + X ^ 7 * 1129 + X ^ 8 * 1054 + X ^ 9 * 430 + X ^ 10 * 631 + X ^ 11 * 438 + X ^ 12 * 1052 + X ^ 13 * 12 + X ^ 14 * 547 + X ^ 15 * 622 + X ^ 16 * 599 + X ^ 17 * 262 + X ^ 18 * 1099
def Mtstep2 : (ZMod 1249)[X] := 916 + X * 281 + X ^ 2 * 858 + X ^ 3 * 25 + X ^ 4 * 533 + X ^ 5 * 557 + X ^ 6 * 1041 + X ^ 7 * 1129 + X ^ 8 * 1054 + X ^ 9 * 430 + X ^ 10 * 631 + X ^ 11 * 438 + X ^ 12 * 1052 + X ^ 13 * 12 + X ^ 14 * 547 + X ^ 15 * 622 + X ^ 16 * 599 + X ^ 17 * 262 + X ^ 18 * 1099
theorem tstep2 : Ltstep2 = Mtstep2 := by
  have hL : Ltstep2.natDegree ≤ 18 := by unfold Ltstep2; compute_degree!
  have hR : Mtstep2.natDegree ≤ 18 := by unfold Mtstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ltstep2, Mtstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ltstep3 : (ZMod 1249)[X] := X * 638 + X ^ 2 * 237 + X ^ 3 * 462 + X ^ 4 * 445 + X ^ 5 * 530 + X ^ 6 * 386 + X ^ 7 * 1217 + X ^ 8 * 766 + X ^ 9 * 682 + X ^ 10 * 825
def Mtstep3 : (ZMod 1249)[X] := X * 638 + X ^ 2 * 237 + X ^ 3 * 462 + X ^ 4 * 445 + X ^ 5 * 530 + X ^ 6 * 386 + X ^ 7 * 1217 + X ^ 8 * 766 + X ^ 9 * 682 + X ^ 10 * 825
theorem tstep3 : Ltstep3 = Mtstep3 := by
  have hL : Ltstep3.natDegree ≤ 18 := by unfold Ltstep3; compute_degree!
  have hR : Mtstep3.natDegree ≤ 18 := by unfold Mtstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ltstep3, Mtstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep0 : (ZMod 1249)[X] := 203 + X * 522 + X ^ 2 * 21 + X ^ 3 * 1047 + X ^ 4 * 377 + X ^ 5 * 577 + X ^ 6 * 1132 + X ^ 7 * 280 + X ^ 8 * 270 + X ^ 9 * 588 + X ^ 10 * 378 + X ^ 11 * 447 + X ^ 12 * 205 + X ^ 13 * 777 + X ^ 14 * 1078 + X ^ 15 * 219 + X ^ 16 * 550 + X ^ 17 * 869 + X ^ 18 * 638
def Mustep0 : (ZMod 1249)[X] := 203 + X * 522 + X ^ 2 * 21 + X ^ 3 * 1047 + X ^ 4 * 377 + X ^ 5 * 577 + X ^ 6 * 1132 + X ^ 7 * 280 + X ^ 8 * 270 + X ^ 9 * 588 + X ^ 10 * 378 + X ^ 11 * 447 + X ^ 12 * 205 + X ^ 13 * 777 + X ^ 14 * 1078 + X ^ 15 * 219 + X ^ 16 * 550 + X ^ 17 * 869 + X ^ 18 * 638
theorem ustep0 : Lustep0 = Mustep0 := by
  have hL : Lustep0.natDegree ≤ 18 := by unfold Lustep0; compute_degree!
  have hR : Mustep0.natDegree ≤ 18 := by unfold Mustep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep0, Mustep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep1 : (ZMod 1249)[X] := 605 + X * 946 + X ^ 2 * 468 + X ^ 3 * 519 + X ^ 4 * 483 + X ^ 5 * 205 + X ^ 6 * 781 + X ^ 7 * 546 + X ^ 8 * 607 + X ^ 9 * 1145 + X ^ 10 * 522 + X ^ 11 * 632 + X ^ 12 * 612 + X ^ 13 * 19 + X ^ 14 * 389 + X ^ 15 * 83 + X ^ 16 * 1182 + X ^ 17 * 490 + X ^ 18 * 209
def Mustep1 : (ZMod 1249)[X] := 605 + X * 946 + X ^ 2 * 468 + X ^ 3 * 519 + X ^ 4 * 483 + X ^ 5 * 205 + X ^ 6 * 781 + X ^ 7 * 546 + X ^ 8 * 607 + X ^ 9 * 1145 + X ^ 10 * 522 + X ^ 11 * 632 + X ^ 12 * 612 + X ^ 13 * 19 + X ^ 14 * 389 + X ^ 15 * 83 + X ^ 16 * 1182 + X ^ 17 * 490 + X ^ 18 * 209
theorem ustep1 : Lustep1 = Mustep1 := by
  have hL : Lustep1.natDegree ≤ 18 := by unfold Lustep1; compute_degree!
  have hR : Mustep1.natDegree ≤ 18 := by unfold Mustep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep1, Mustep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep2 : (ZMod 1249)[X] := 204 + X * 264 + X ^ 2 * 920 + X ^ 3 * 996 + X ^ 4 * 549 + X ^ 5 * 1011 + X ^ 6 * 916 + X ^ 7 * 91 + X ^ 8 * 1069 + X ^ 9 * 700 + X ^ 10 * 920 + X ^ 11 * 1156 + X ^ 12 * 167 + X ^ 13 * 31 + X ^ 14 * 31 + X ^ 15 * 33 + X ^ 16 * 18 + X ^ 17 * 272 + X ^ 18 * 544
def Mustep2 : (ZMod 1249)[X] := 204 + X * 264 + X ^ 2 * 920 + X ^ 3 * 996 + X ^ 4 * 549 + X ^ 5 * 1011 + X ^ 6 * 916 + X ^ 7 * 91 + X ^ 8 * 1069 + X ^ 9 * 700 + X ^ 10 * 920 + X ^ 11 * 1156 + X ^ 12 * 167 + X ^ 13 * 31 + X ^ 14 * 31 + X ^ 15 * 33 + X ^ 16 * 18 + X ^ 17 * 272 + X ^ 18 * 544
theorem ustep2 : Lustep2 = Mustep2 := by
  have hL : Lustep2.natDegree ≤ 18 := by unfold Lustep2; compute_degree!
  have hR : Mustep2.natDegree ≤ 18 := by unfold Mustep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep2, Mustep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep3 : (ZMod 1249)[X] := 79 + X * 91 + X ^ 2 * 877 + X ^ 3 * 405 + X ^ 4 * 588 + X ^ 5 * 1088 + X ^ 6 * 97 + X ^ 7 * 1035 + X ^ 8 * 686 + X ^ 9 * 304 + X ^ 10 * 43 + X ^ 11 * 667 + X ^ 12 * 1022 + X ^ 13 * 391 + X ^ 14 * 64 + X ^ 15 * 947 + X ^ 16 * 79 + X ^ 17 * 687 + X ^ 18 * 939
def Mustep3 : (ZMod 1249)[X] := 79 + X * 91 + X ^ 2 * 877 + X ^ 3 * 405 + X ^ 4 * 588 + X ^ 5 * 1088 + X ^ 6 * 97 + X ^ 7 * 1035 + X ^ 8 * 686 + X ^ 9 * 304 + X ^ 10 * 43 + X ^ 11 * 667 + X ^ 12 * 1022 + X ^ 13 * 391 + X ^ 14 * 64 + X ^ 15 * 947 + X ^ 16 * 79 + X ^ 17 * 687 + X ^ 18 * 939
theorem ustep3 : Lustep3 = Mustep3 := by
  have hL : Lustep3.natDegree ≤ 18 := by unfold Lustep3; compute_degree!
  have hR : Mustep3.natDegree ≤ 18 := by unfold Mustep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep3, Mustep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep4 : (ZMod 1249)[X] := 96 + X * 541 + X ^ 2 * 975 + X ^ 3 * 769 + X ^ 4 * 199 + X ^ 5 * 503 + X ^ 6 * 402 + X ^ 7 * 1189 + X ^ 8 * 361 + X ^ 9 * 787 + X ^ 10 * 584 + X ^ 11 * 1119 + X ^ 12 * 207 + X ^ 13 * 410 + X ^ 14 * 489 + X ^ 15 * 1171 + X ^ 16 * 397 + X ^ 17 * 896 + X ^ 18 * 611
def Mustep4 : (ZMod 1249)[X] := 96 + X * 541 + X ^ 2 * 975 + X ^ 3 * 769 + X ^ 4 * 199 + X ^ 5 * 503 + X ^ 6 * 402 + X ^ 7 * 1189 + X ^ 8 * 361 + X ^ 9 * 787 + X ^ 10 * 584 + X ^ 11 * 1119 + X ^ 12 * 207 + X ^ 13 * 410 + X ^ 14 * 489 + X ^ 15 * 1171 + X ^ 16 * 397 + X ^ 17 * 896 + X ^ 18 * 611
theorem ustep4 : Lustep4 = Mustep4 := by
  have hL : Lustep4.natDegree ≤ 18 := by unfold Lustep4; compute_degree!
  have hR : Mustep4.natDegree ≤ 18 := by unfold Mustep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep4, Mustep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep5 : (ZMod 1249)[X] := 1155 + X * 1117 + X ^ 2 * 950 + X ^ 3 * 1219 + X ^ 4 * 525 + X ^ 5 * 69 + X ^ 6 * 984 + X ^ 7 * 1004 + X ^ 8 * 237 + X ^ 9 * 587 + X ^ 10 * 452 + X ^ 11 * 840 + X ^ 12 * 130 + X ^ 13 * 977 + X ^ 14 * 751 + X ^ 15 * 740 + X ^ 16 * 357 + X ^ 17 * 1082 + X ^ 18 * 1049
def Mustep5 : (ZMod 1249)[X] := 1155 + X * 1117 + X ^ 2 * 950 + X ^ 3 * 1219 + X ^ 4 * 525 + X ^ 5 * 69 + X ^ 6 * 984 + X ^ 7 * 1004 + X ^ 8 * 237 + X ^ 9 * 587 + X ^ 10 * 452 + X ^ 11 * 840 + X ^ 12 * 130 + X ^ 13 * 977 + X ^ 14 * 751 + X ^ 15 * 740 + X ^ 16 * 357 + X ^ 17 * 1082 + X ^ 18 * 1049
theorem ustep5 : Lustep5 = Mustep5 := by
  have hL : Lustep5.natDegree ≤ 18 := by unfold Lustep5; compute_degree!
  have hR : Mustep5.natDegree ≤ 18 := by unfold Mustep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep5, Mustep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep6 : (ZMod 1249)[X] := 780 + X * 790 + X ^ 2 * 886 + X ^ 3 * 300 + X ^ 4 * 666 + X ^ 5 * 311 + X ^ 6 * 809 + X ^ 7 * 498 + X ^ 8 * 333 + X ^ 9 * 1196 + X ^ 10 * 1243 + X ^ 11 * 136 + X ^ 12 * 1055 + X ^ 13 * 699 + X ^ 14 * 704 + X ^ 15 * 439 + X ^ 16 * 966 + X ^ 17 * 1090 + X ^ 18 * 701
def Mustep6 : (ZMod 1249)[X] := 780 + X * 790 + X ^ 2 * 886 + X ^ 3 * 300 + X ^ 4 * 666 + X ^ 5 * 311 + X ^ 6 * 809 + X ^ 7 * 498 + X ^ 8 * 333 + X ^ 9 * 1196 + X ^ 10 * 1243 + X ^ 11 * 136 + X ^ 12 * 1055 + X ^ 13 * 699 + X ^ 14 * 704 + X ^ 15 * 439 + X ^ 16 * 966 + X ^ 17 * 1090 + X ^ 18 * 701
theorem ustep6 : Lustep6 = Mustep6 := by
  have hL : Lustep6.natDegree ≤ 18 := by unfold Lustep6; compute_degree!
  have hR : Mustep6.natDegree ≤ 18 := by unfold Mustep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep6, Mustep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep7 : (ZMod 1249)[X] := 313 + X * 1058 + X ^ 2 * 606 + X ^ 3 * 5 + X ^ 4 * 589 + X ^ 5 * 1192 + X ^ 6 * 493 + X ^ 7 * 259 + X ^ 8 * 1232 + X ^ 9 * 1111 + X ^ 10 * 444 + X ^ 11 * 807 + X ^ 12 * 376 + X ^ 13 * 381 + X ^ 14 * 540 + X ^ 15 * 908 + X ^ 16 * 315 + X ^ 17 * 861 + X ^ 18 * 844
def Mustep7 : (ZMod 1249)[X] := 313 + X * 1058 + X ^ 2 * 606 + X ^ 3 * 5 + X ^ 4 * 589 + X ^ 5 * 1192 + X ^ 6 * 493 + X ^ 7 * 259 + X ^ 8 * 1232 + X ^ 9 * 1111 + X ^ 10 * 444 + X ^ 11 * 807 + X ^ 12 * 376 + X ^ 13 * 381 + X ^ 14 * 540 + X ^ 15 * 908 + X ^ 16 * 315 + X ^ 17 * 861 + X ^ 18 * 844
theorem ustep7 : Lustep7 = Mustep7 := by
  have hL : Lustep7.natDegree ≤ 18 := by unfold Lustep7; compute_degree!
  have hR : Mustep7.natDegree ≤ 18 := by unfold Mustep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep7, Mustep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep8 : (ZMod 1249)[X] := 523 + X * 480 + X ^ 2 * 253 + X ^ 3 * 686 + X ^ 4 * 616 + X ^ 5 * 857 + X ^ 6 * 259 + X ^ 7 * 364 + X ^ 8 * 491 + X ^ 9 * 376 + X ^ 10 * 909 + X ^ 11 * 455 + X ^ 12 * 762 + X ^ 13 * 1153 + X ^ 14 * 144 + X ^ 15 * 865 + X ^ 16 * 533 + X ^ 17 * 715 + X ^ 18 * 1112
def Mustep8 : (ZMod 1249)[X] := 523 + X * 480 + X ^ 2 * 253 + X ^ 3 * 686 + X ^ 4 * 616 + X ^ 5 * 857 + X ^ 6 * 259 + X ^ 7 * 364 + X ^ 8 * 491 + X ^ 9 * 376 + X ^ 10 * 909 + X ^ 11 * 455 + X ^ 12 * 762 + X ^ 13 * 1153 + X ^ 14 * 144 + X ^ 15 * 865 + X ^ 16 * 533 + X ^ 17 * 715 + X ^ 18 * 1112
theorem ustep8 : Lustep8 = Mustep8 := by
  have hL : Lustep8.natDegree ≤ 18 := by unfold Lustep8; compute_degree!
  have hR : Mustep8.natDegree ≤ 18 := by unfold Mustep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep8, Mustep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lustep9 : (ZMod 1249)[X] := 771 + X * 1194 + X ^ 2 * 960 + X ^ 3 * 1045 + X ^ 4 * 278 + X ^ 5 * 386 + X ^ 6 * 524 + X ^ 7 * 836 + X ^ 8 * 91 + X ^ 9 * 107 + X ^ 10 * 23 + X ^ 11 * 1242 + X ^ 12 * 160 + X ^ 13 * 136 + X ^ 14 * 788 + X ^ 15 * 1236 + X ^ 16 * 472 + X ^ 17 * 896 + X ^ 18 * 1105
def Mustep9 : (ZMod 1249)[X] := 771 + X * 1194 + X ^ 2 * 960 + X ^ 3 * 1045 + X ^ 4 * 278 + X ^ 5 * 386 + X ^ 6 * 524 + X ^ 7 * 836 + X ^ 8 * 91 + X ^ 9 * 107 + X ^ 10 * 23 + X ^ 11 * 1242 + X ^ 12 * 160 + X ^ 13 * 136 + X ^ 14 * 788 + X ^ 15 * 1236 + X ^ 16 * 472 + X ^ 17 * 896 + X ^ 18 * 1105
theorem ustep9 : Lustep9 = Mustep9 := by
  have hL : Lustep9.natDegree ≤ 18 := by unfold Lustep9; compute_degree!
  have hR : Mustep9.natDegree ≤ 18 := by unfold Mustep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lustep9, Mustep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2561Batch2Actual

end