import tmp.sheaf.xif.paper.S2562Batch3Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2562Batch3Actual

namespace LeanFormal.IUT.XiFPaper.S2563Batch4Actual

def A0 : (ZMod 1249)[X] := 292 + X * 107 + X ^ 2 * 397 + X ^ 3 * 634 + X ^ 4 * 925 + X ^ 5 * 322 + X ^ 6 * 524 + X ^ 7 * 1173 + X ^ 8 * 157 + X ^ 9 * 457
def A1 : (ZMod 1249)[X] := 686 + X * 832 + X ^ 2 * 55 + X ^ 3 * 574 + X ^ 4 * 937 + X ^ 5 * 980 + X ^ 6 * 438 + X ^ 7 * 1082 + X ^ 8 * 51 + X ^ 9 * 600
def A2 : (ZMod 1249)[X] := 401 + X * 538 + X ^ 2 * 839 + X ^ 3 * 415 + X ^ 4 * 610 + X ^ 5 * 23 + X ^ 6 * 12 + X ^ 7 * 1020 + X ^ 8 * 719 + X ^ 9 * 460
def A3 : (ZMod 1249)[X] := 431 + X * 1161 + X ^ 2 * 526 + X ^ 3 * 1234 + X ^ 4 * 140 + X ^ 5 * 235 + X ^ 6 * 742 + X ^ 7 * 1025 + X ^ 8 * 290 + X ^ 9 * 79
def A4 : (ZMod 1249)[X] := 352 + X * 513 + X ^ 2 * 68 + X ^ 3 * 465 + X ^ 4 * 393 + X ^ 5 * 933 + X ^ 6 * 1104 + X ^ 7 * 967 + X ^ 8 * 1129 + X ^ 9 * 713
def Lastep0 : (ZMod 1249)[X] := 1062 + X * 363 + X ^ 2 * 609 + X ^ 3 * 112 + X ^ 4 * 1118 + X ^ 5 * 335 + X ^ 6 * 262 + X ^ 7 * 210 + X ^ 8 * 712 + X ^ 9 * 1247 + X ^ 10 * 817 + X ^ 11 * 526 + X ^ 12 * 504 + X ^ 13 * 612 + X ^ 14 * 851 + X ^ 15 * 491 + X ^ 16 * 681 + X ^ 17 * 69 + X ^ 18 * 1121
def Mastep0 : (ZMod 1249)[X] := 1062 + X * 363 + X ^ 2 * 609 + X ^ 3 * 112 + X ^ 4 * 1118 + X ^ 5 * 335 + X ^ 6 * 262 + X ^ 7 * 210 + X ^ 8 * 712 + X ^ 9 * 1247 + X ^ 10 * 817 + X ^ 11 * 526 + X ^ 12 * 504 + X ^ 13 * 612 + X ^ 14 * 851 + X ^ 15 * 491 + X ^ 16 * 681 + X ^ 17 * 69 + X ^ 18 * 1121
theorem astep0 : Lastep0 = Mastep0 := by
  have hL : Lastep0.natDegree ≤ 18 := by unfold Lastep0; compute_degree!
  have hR : Mastep0.natDegree ≤ 18 := by unfold Mastep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lastep0, Mastep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lastep1 : (ZMod 1249)[X] := 750 + X * 1221 + X ^ 2 * 1052 + X ^ 3 * 123 + X ^ 4 * 341 + X ^ 5 * 555 + X ^ 6 * 343 + X ^ 7 * 321 + X ^ 8 * 48 + X ^ 9 * 799 + X ^ 10 * 1021 + X ^ 11 * 961 + X ^ 12 * 173 + X ^ 13 * 1128 + X ^ 14 * 589 + X ^ 15 * 374 + X ^ 16 * 614 + X ^ 17 * 1108 + X ^ 18 * 215
def Mastep1 : (ZMod 1249)[X] := 750 + X * 1221 + X ^ 2 * 1052 + X ^ 3 * 123 + X ^ 4 * 341 + X ^ 5 * 555 + X ^ 6 * 343 + X ^ 7 * 321 + X ^ 8 * 48 + X ^ 9 * 799 + X ^ 10 * 1021 + X ^ 11 * 961 + X ^ 12 * 173 + X ^ 13 * 1128 + X ^ 14 * 589 + X ^ 15 * 374 + X ^ 16 * 614 + X ^ 17 * 1108 + X ^ 18 * 215
theorem astep1 : Lastep1 = Mastep1 := by
  have hL : Lastep1.natDegree ≤ 18 := by unfold Lastep1; compute_degree!
  have hR : Mastep1.natDegree ≤ 18 := by unfold Mastep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lastep1, Mastep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lastep2 : (ZMod 1249)[X] := 875 + X * 849 + X ^ 2 * 690 + X ^ 3 * 1020 + X ^ 4 * 408 + X ^ 5 * 526 + X ^ 6 * 660 + X ^ 7 * 1242 + X ^ 8 * 934 + X ^ 9 * 124 + X ^ 10 * 986 + X ^ 11 * 283 + X ^ 12 * 678 + X ^ 13 * 674 + X ^ 14 * 1124 + X ^ 15 * 315 + X ^ 16 * 855 + X ^ 17 * 397 + X ^ 18 * 980
def Mastep2 : (ZMod 1249)[X] := 875 + X * 849 + X ^ 2 * 690 + X ^ 3 * 1020 + X ^ 4 * 408 + X ^ 5 * 526 + X ^ 6 * 660 + X ^ 7 * 1242 + X ^ 8 * 934 + X ^ 9 * 124 + X ^ 10 * 986 + X ^ 11 * 283 + X ^ 12 * 678 + X ^ 13 * 674 + X ^ 14 * 1124 + X ^ 15 * 315 + X ^ 16 * 855 + X ^ 17 * 397 + X ^ 18 * 980
theorem astep2 : Lastep2 = Mastep2 := by
  have hL : Lastep2.natDegree ≤ 18 := by unfold Lastep2; compute_degree!
  have hR : Mastep2.natDegree ≤ 18 := by unfold Mastep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lastep2, Mastep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lastep3 : (ZMod 1249)[X] := 701 + X * 856 + X ^ 2 * 175 + X ^ 3 * 839 + X ^ 4 * 1162 + X ^ 5 * 1176 + X ^ 6 * 66 + X ^ 7 * 1145 + X ^ 8 * 587 + X ^ 9 * 373 + X ^ 10 * 938 + X ^ 11 * 718 + X ^ 12 * 176 + X ^ 13 * 830 + X ^ 14 * 625 + X ^ 15 * 788 + X ^ 16 * 861 + X ^ 17 * 362 + X ^ 18 * 1238
def Mastep3 : (ZMod 1249)[X] := 701 + X * 856 + X ^ 2 * 175 + X ^ 3 * 839 + X ^ 4 * 1162 + X ^ 5 * 1176 + X ^ 6 * 66 + X ^ 7 * 1145 + X ^ 8 * 587 + X ^ 9 * 373 + X ^ 10 * 938 + X ^ 11 * 718 + X ^ 12 * 176 + X ^ 13 * 830 + X ^ 14 * 625 + X ^ 15 * 788 + X ^ 16 * 861 + X ^ 17 * 362 + X ^ 18 * 1238
theorem astep3 : Lastep3 = Mastep3 := by
  have hL : Lastep3.natDegree ≤ 18 := by unfold Lastep3; compute_degree!
  have hR : Mastep3.natDegree ≤ 18 := by unfold Mastep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lastep3, Mastep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def B0 : (ZMod 1249)[X] := 352 + X * 513 + X ^ 2 * 68 + X ^ 3 * 465 + X ^ 4 * 393 + X ^ 5 * 933 + X ^ 6 * 1104 + X ^ 7 * 967 + X ^ 8 * 1129 + X ^ 9 * 713
def B1 : (ZMod 1249)[X] := 32 + X * 669 + X ^ 2 * 509 + X ^ 3 * 380 + X ^ 4 * 45 + X ^ 5 * 1226 + X ^ 6 * 3 + X ^ 7 * 546 + X ^ 8 * 1194 + X ^ 9 * 190
def B2 : (ZMod 1249)[X] := 151 + X * 562 + X ^ 2 * 504 + X ^ 3 * 618 + X ^ 4 * 838 + X ^ 5 * 1226 + X ^ 6 * 933 + X ^ 7 * 464 + X ^ 8 * 442 + X ^ 9 * 799
def B3 : (ZMod 1249)[X] := 794 + X * 238 + X ^ 2 * 76 + X ^ 3 * 212 + X ^ 4 * 506 + X ^ 5 * 524 + X ^ 6 * 703 + X ^ 7 * 984 + X ^ 8 * 239 + X ^ 9 * 455
def B4 : (ZMod 1249)[X] := 568 + X * 527 + X ^ 2 * 1053 + X ^ 3 * 347 + X ^ 4 * 937 + X ^ 5 * 314 + X ^ 6 * 386 + X ^ 7 * 457 + X ^ 8 * 149 + X ^ 9 * 594
def B5 : (ZMod 1249)[X] := 364 + X * 743 + X ^ 2 * 643 + X ^ 3 * 733 + X ^ 4 * 770 + X ^ 5 * 564 + X ^ 6 * 85 + X ^ 7 * 785 + X ^ 8 * 1017 + X ^ 9 * 523
def B6 : (ZMod 1249)[X] := 1179 + X * 590 + X ^ 2 * 958 + X ^ 3 * 616 + X ^ 4 * 785 + X ^ 5 * 340 + X ^ 6 * 668 + X ^ 7 * 821 + X ^ 8 * 525 + X ^ 9 * 556
def B7 : (ZMod 1249)[X] := 676 + X * 215 + X ^ 2 * 455 + X ^ 3 * 724 + X ^ 4 * 116 + X ^ 5 * 1068 + X ^ 6 * 159 + X ^ 7 * 176 + X ^ 8 * 858 + X ^ 9 * 1132
def B8 : (ZMod 1249)[X] := 691 + X * 509 + X ^ 2 * 517 + X ^ 3 * 810 + X ^ 4 * 1170 + X ^ 5 * 151 + X ^ 6 * 280 + X ^ 7 * 426 + X ^ 8 * 133 + X ^ 9 * 41
def B9 : (ZMod 1249)[X] := 856 + X * 1048 + X ^ 2 * 844 + X ^ 3 * 1112 + X ^ 4 * 24 + X ^ 5 * 1084 + X ^ 6 * 664 + X ^ 7 * 104 + X ^ 8 * 1041 + X ^ 9 * 41
def B10 : (ZMod 1249)[X] := 794 + X * 903 + X ^ 2 * 1242 + X ^ 3 * 100 + X ^ 4 * 526 + X ^ 5 * 715 + X ^ 6 * 798 + X ^ 7 * 237 + X ^ 8 * 993 + X ^ 9 * 685
def Lbstep0 : (ZMod 1249)[X] := 253 + X * 191 + X ^ 2 * 40 + X ^ 3 * 1195 + X ^ 4 * 243 + X ^ 5 * 439 + X ^ 6 * 751 + X ^ 7 * 196 + X ^ 8 * 360 + X ^ 9 * 969 + X ^ 10 * 445 + X ^ 11 * 240 + X ^ 12 * 1133 + X ^ 13 * 1112 + X ^ 14 * 938 + X ^ 15 * 798 + X ^ 16 * 707 + X ^ 17 * 1242 + X ^ 18 * 26
def Mbstep0 : (ZMod 1249)[X] := 253 + X * 191 + X ^ 2 * 40 + X ^ 3 * 1195 + X ^ 4 * 243 + X ^ 5 * 439 + X ^ 6 * 751 + X ^ 7 * 196 + X ^ 8 * 360 + X ^ 9 * 969 + X ^ 10 * 445 + X ^ 11 * 240 + X ^ 12 * 1133 + X ^ 13 * 1112 + X ^ 14 * 938 + X ^ 15 * 798 + X ^ 16 * 707 + X ^ 17 * 1242 + X ^ 18 * 26
theorem bstep0 : Lbstep0 = Mbstep0 := by
  have hL : Lbstep0.natDegree ≤ 18 := by unfold Lbstep0; compute_degree!
  have hR : Mbstep0.natDegree ≤ 18 := by unfold Mbstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep0, Mbstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep1 : (ZMod 1249)[X] := 1024 + X * 350 + X ^ 2 * 521 + X ^ 3 * 926 + X ^ 4 * 1017 + X ^ 5 * 934 + X ^ 6 * 1005 + X ^ 7 * 1033 + X ^ 8 * 199 + X ^ 9 * 4 + X ^ 10 * 730 + X ^ 11 * 782 + X ^ 12 * 684 + X ^ 13 * 424 + X ^ 14 * 527 + X ^ 15 * 1032 + X ^ 16 * 673 + X ^ 17 * 333 + X ^ 18 * 1128
def Mbstep1 : (ZMod 1249)[X] := 1024 + X * 350 + X ^ 2 * 521 + X ^ 3 * 926 + X ^ 4 * 1017 + X ^ 5 * 934 + X ^ 6 * 1005 + X ^ 7 * 1033 + X ^ 8 * 199 + X ^ 9 * 4 + X ^ 10 * 730 + X ^ 11 * 782 + X ^ 12 * 684 + X ^ 13 * 424 + X ^ 14 * 527 + X ^ 15 * 1032 + X ^ 16 * 673 + X ^ 17 * 333 + X ^ 18 * 1128
theorem bstep1 : Lbstep1 = Mbstep1 := by
  have hL : Lbstep1.natDegree ≤ 18 := by unfold Lbstep1; compute_degree!
  have hR : Mbstep1.natDegree ≤ 18 := by unfold Mbstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep1, Mbstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep2 : (ZMod 1249)[X] := 319 + X * 1109 + X ^ 2 * 926 + X ^ 3 * 1234 + X ^ 4 * 186 + X ^ 5 * 407 + X ^ 6 * 1228 + X ^ 7 * 666 + X ^ 8 * 1116 + X ^ 9 * 1065 + X ^ 10 * 390 + X ^ 11 * 620 + X ^ 12 * 814 + X ^ 13 * 115 + X ^ 14 * 367 + X ^ 15 * 132 + X ^ 16 * 86 + X ^ 17 * 631 + X ^ 18 * 162
def Mbstep2 : (ZMod 1249)[X] := 319 + X * 1109 + X ^ 2 * 926 + X ^ 3 * 1234 + X ^ 4 * 186 + X ^ 5 * 407 + X ^ 6 * 1228 + X ^ 7 * 666 + X ^ 8 * 1116 + X ^ 9 * 1065 + X ^ 10 * 390 + X ^ 11 * 620 + X ^ 12 * 814 + X ^ 13 * 115 + X ^ 14 * 367 + X ^ 15 * 132 + X ^ 16 * 86 + X ^ 17 * 631 + X ^ 18 * 162
theorem bstep2 : Lbstep2 = Mbstep2 := by
  have hL : Lbstep2.natDegree ≤ 18 := by unfold Lbstep2; compute_degree!
  have hR : Mbstep2.natDegree ≤ 18 := by unfold Mbstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep2, Mbstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep3 : (ZMod 1249)[X] := 940 + X * 746 + X ^ 2 * 1223 + X ^ 3 * 630 + X ^ 4 * 944 + X ^ 5 * 1076 + X ^ 6 * 85 + X ^ 7 * 666 + X ^ 8 * 381 + X ^ 9 * 684 + X ^ 10 * 1211 + X ^ 11 * 821 + X ^ 12 * 548 + X ^ 13 * 1112 + X ^ 14 * 56 + X ^ 15 * 970 + X ^ 16 * 823 + X ^ 17 * 164 + X ^ 18 * 940
def Mbstep3 : (ZMod 1249)[X] := 940 + X * 746 + X ^ 2 * 1223 + X ^ 3 * 630 + X ^ 4 * 944 + X ^ 5 * 1076 + X ^ 6 * 85 + X ^ 7 * 666 + X ^ 8 * 381 + X ^ 9 * 684 + X ^ 10 * 1211 + X ^ 11 * 821 + X ^ 12 * 548 + X ^ 13 * 1112 + X ^ 14 * 56 + X ^ 15 * 970 + X ^ 16 * 823 + X ^ 17 * 164 + X ^ 18 * 940
theorem bstep3 : Lbstep3 = Mbstep3 := by
  have hL : Lbstep3.natDegree ≤ 18 := by unfold Lbstep3; compute_degree!
  have hR : Mbstep3.natDegree ≤ 18 := by unfold Mbstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep3, Mbstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep4 : (ZMod 1249)[X] := 382 + X * 401 + X ^ 2 * 117 + X ^ 3 * 258 + X ^ 4 * 1011 + X ^ 5 * 495 + X ^ 6 * 475 + X ^ 7 * 599 + X ^ 8 * 542 + X ^ 9 * 214 + X ^ 10 * 652 + X ^ 11 * 160 + X ^ 12 * 856 + X ^ 13 * 780 + X ^ 14 * 1216 + X ^ 15 * 230 + X ^ 16 * 569 + X ^ 17 * 903 + X ^ 18 * 618
def Mbstep4 : (ZMod 1249)[X] := 382 + X * 401 + X ^ 2 * 117 + X ^ 3 * 258 + X ^ 4 * 1011 + X ^ 5 * 495 + X ^ 6 * 475 + X ^ 7 * 599 + X ^ 8 * 542 + X ^ 9 * 214 + X ^ 10 * 652 + X ^ 11 * 160 + X ^ 12 * 856 + X ^ 13 * 780 + X ^ 14 * 1216 + X ^ 15 * 230 + X ^ 16 * 569 + X ^ 17 * 903 + X ^ 18 * 618
theorem bstep4 : Lbstep4 = Mbstep4 := by
  have hL : Lbstep4.natDegree ≤ 18 := by unfold Lbstep4; compute_degree!
  have hR : Mbstep4.natDegree ≤ 18 := by unfold Mbstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep4, Mbstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep5 : (ZMod 1249)[X] := 102 + X * 87 + X ^ 2 * 969 + X ^ 3 * 314 + X ^ 4 * 1148 + X ^ 5 * 699 + X ^ 6 * 686 + X ^ 7 * 207 + X ^ 8 * 1170 + X ^ 9 * 304 + X ^ 10 * 296 + X ^ 11 * 1056 + X ^ 12 * 685 + X ^ 13 * 216 + X ^ 14 * 163 + X ^ 15 * 699 + X ^ 16 * 634 + X ^ 17 * 883 + X ^ 18 * 1247
def Mbstep5 : (ZMod 1249)[X] := 102 + X * 87 + X ^ 2 * 969 + X ^ 3 * 314 + X ^ 4 * 1148 + X ^ 5 * 699 + X ^ 6 * 686 + X ^ 7 * 207 + X ^ 8 * 1170 + X ^ 9 * 304 + X ^ 10 * 296 + X ^ 11 * 1056 + X ^ 12 * 685 + X ^ 13 * 216 + X ^ 14 * 163 + X ^ 15 * 699 + X ^ 16 * 634 + X ^ 17 * 883 + X ^ 18 * 1247
theorem bstep5 : Lbstep5 = Mbstep5 := by
  have hL : Lbstep5.natDegree ≤ 18 := by unfold Lbstep5; compute_degree!
  have hR : Mbstep5.natDegree ≤ 18 := by unfold Mbstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep5, Mbstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep6 : (ZMod 1249)[X] := 1153 + X * 1083 + X ^ 2 * 401 + X ^ 3 * 36 + X ^ 4 * 972 + X ^ 5 * 604 + X ^ 6 * 450 + X ^ 7 * 1194 + X ^ 8 * 343 + X ^ 9 * 501 + X ^ 10 * 884 + X ^ 11 * 572 + X ^ 12 * 758 + X ^ 13 * 1138 + X ^ 14 * 1174 + X ^ 15 * 1150 + X ^ 16 * 778 + X ^ 17 * 517 + X ^ 18 * 633
def Mbstep6 : (ZMod 1249)[X] := 1153 + X * 1083 + X ^ 2 * 401 + X ^ 3 * 36 + X ^ 4 * 972 + X ^ 5 * 604 + X ^ 6 * 450 + X ^ 7 * 1194 + X ^ 8 * 343 + X ^ 9 * 501 + X ^ 10 * 884 + X ^ 11 * 572 + X ^ 12 * 758 + X ^ 13 * 1138 + X ^ 14 * 1174 + X ^ 15 * 1150 + X ^ 16 * 778 + X ^ 17 * 517 + X ^ 18 * 633
theorem bstep6 : Lbstep6 = Mbstep6 := by
  have hL : Lbstep6.natDegree ≤ 18 := by unfold Lbstep6; compute_degree!
  have hR : Mbstep6.natDegree ≤ 18 := by unfold Mbstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep6, Mbstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep7 : (ZMod 1249)[X] := 1091 + X * 912 + X ^ 2 * 664 + X ^ 3 * 438 + X ^ 4 * 717 + X ^ 5 * 629 + X ^ 6 * 1237 + X ^ 7 * 1077 + X ^ 8 * 160 + X ^ 9 * 853 + X ^ 10 * 811 + X ^ 11 * 84 + X ^ 12 * 1201 + X ^ 13 * 502 + X ^ 14 * 201 + X ^ 15 * 22 + X ^ 16 * 536 + X ^ 17 * 317 + X ^ 18 * 1199
def Mbstep7 : (ZMod 1249)[X] := 1091 + X * 912 + X ^ 2 * 664 + X ^ 3 * 438 + X ^ 4 * 717 + X ^ 5 * 629 + X ^ 6 * 1237 + X ^ 7 * 1077 + X ^ 8 * 160 + X ^ 9 * 853 + X ^ 10 * 811 + X ^ 11 * 84 + X ^ 12 * 1201 + X ^ 13 * 502 + X ^ 14 * 201 + X ^ 15 * 22 + X ^ 16 * 536 + X ^ 17 * 317 + X ^ 18 * 1199
theorem bstep7 : Lbstep7 = Mbstep7 := by
  have hL : Lbstep7.natDegree ≤ 18 := by unfold Lbstep7; compute_degree!
  have hR : Mbstep7.natDegree ≤ 18 := by unfold Mbstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep7, Mbstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep8 : (ZMod 1249)[X] := 363 + X * 251 + X ^ 2 * 604 + X ^ 3 * 793 + X ^ 4 * 977 + X ^ 5 * 323 + X ^ 6 * 984 + X ^ 7 * 148 + X ^ 8 * 32 + X ^ 9 * 632 + X ^ 10 * 1119 + X ^ 11 * 326 + X ^ 12 * 160 + X ^ 13 * 1215 + X ^ 14 * 1052 + X ^ 15 * 135 + X ^ 16 * 163 + X ^ 17 * 914 + X ^ 18 * 432
def Mbstep8 : (ZMod 1249)[X] := 363 + X * 251 + X ^ 2 * 604 + X ^ 3 * 793 + X ^ 4 * 977 + X ^ 5 * 323 + X ^ 6 * 984 + X ^ 7 * 148 + X ^ 8 * 32 + X ^ 9 * 632 + X ^ 10 * 1119 + X ^ 11 * 326 + X ^ 12 * 160 + X ^ 13 * 1215 + X ^ 14 * 1052 + X ^ 15 * 135 + X ^ 16 * 163 + X ^ 17 * 914 + X ^ 18 * 432
theorem bstep8 : Lbstep8 = Mbstep8 := by
  have hL : Lbstep8.natDegree ≤ 18 := by unfold Lbstep8; compute_degree!
  have hR : Mbstep8.natDegree ≤ 18 := by unfold Mbstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep8, Mbstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lbstep9 : (ZMod 1249)[X] := 822 + X * 612 + X ^ 2 * 268 + X ^ 3 * 708 + X ^ 4 * 395 + X ^ 5 * 1196 + X ^ 6 * 889 + X ^ 7 * 724 + X ^ 8 * 579 + X ^ 9 * 865 + X ^ 10 * 245 + X ^ 11 * 751 + X ^ 12 * 666 + X ^ 13 * 137 + X ^ 14 * 838 + X ^ 15 * 1192 + X ^ 16 * 583 + X ^ 17 * 430 + X ^ 18 * 432
def Mbstep9 : (ZMod 1249)[X] := 822 + X * 612 + X ^ 2 * 268 + X ^ 3 * 708 + X ^ 4 * 395 + X ^ 5 * 1196 + X ^ 6 * 889 + X ^ 7 * 724 + X ^ 8 * 579 + X ^ 9 * 865 + X ^ 10 * 245 + X ^ 11 * 751 + X ^ 12 * 666 + X ^ 13 * 137 + X ^ 14 * 838 + X ^ 15 * 1192 + X ^ 16 * 583 + X ^ 17 * 430 + X ^ 18 * 432
theorem bstep9 : Lbstep9 = Mbstep9 := by
  have hL : Lbstep9.natDegree ≤ 18 := by unfold Lbstep9; compute_degree!
  have hR : Mbstep9.natDegree ≤ 18 := by unfold Mbstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lbstep9, Mbstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2563Batch4Actual

end