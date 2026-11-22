import tmp.sheaf.xif.paper.S2565Batch6Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2565Batch6Actual

namespace LeanFormal.IUT.XiFPaper.S2566Batch7Actual

def G0 : (ZMod 1249)[X] := 1216 + X * 331 + X ^ 2 * 278 + X ^ 3 * 582 + X ^ 4 * 778 + X ^ 5 * 897 + X ^ 6 * 168 + X ^ 7 * 698 + X ^ 8 * 790 + X ^ 9 * 994
def G1 : (ZMod 1249)[X] := 872 + X * 286 + X ^ 2 * 575 + X ^ 3 * 406 + X ^ 4 * 779 + X ^ 5 * 1162 + X ^ 6 * 313 + X ^ 7 * 1007 + X ^ 8 * 1153 + X ^ 9 * 339
def G2 : (ZMod 1249)[X] := 607 + X * 523 + X ^ 2 * 428 + X ^ 3 * 414 + X ^ 4 * 312 + X ^ 5 * 371 + X ^ 6 * 775 + X ^ 7 * 438 + X ^ 8 * 1231 + X ^ 9 * 202
def G3 : (ZMod 1249)[X] := 172 + X * 268 + X ^ 2 * 811 + X ^ 3 * 6 + X ^ 4 * 349 + X ^ 5 * 1041 + X ^ 6 * 65 + X ^ 7 * 1161 + X ^ 8 * 352 + X ^ 9 * 872
def G4 : (ZMod 1249)[X] := 27 + X * 119 + X ^ 2 * 1099 + X ^ 3 * 980 + X ^ 4 * 92 + X ^ 5 * 377 + X ^ 6 * 288 + X ^ 7 * 614 + X ^ 8 * 443 + X ^ 9 * 183
def G5 : (ZMod 1249)[X] := 490 + X * 421 + X ^ 2 * 975 + X ^ 3 * 1142 + X ^ 4 * 466 + X ^ 5 * 1199 + X ^ 6 * 198 + X ^ 7 * 62 + X ^ 8 * 458 + X ^ 9 * 760
def G6 : (ZMod 1249)[X] := 99 + X * 791 + X ^ 2 * 674 + X ^ 3 * 537 + X ^ 4 * 176 + X ^ 5 * 245 + X ^ 6 * 23 + X ^ 7 * 411 + X ^ 8 * 244 + X ^ 9 * 507
def G7 : (ZMod 1249)[X] := 638 + X * 1018 + X ^ 2 * 29 + X ^ 3 * 479 + X ^ 4 * 672 + X ^ 5 * 1097 + X ^ 6 * 460 + X ^ 7 * 941 + X ^ 8 * 757 + X ^ 9 * 986
def G8 : (ZMod 1249)[X] := 109 + X * 445 + X ^ 2 * 799 + X ^ 3 * 783 + X ^ 4 * 935 + X ^ 5 * 228 + X ^ 6 * 283 + X ^ 7 * 1048 + X ^ 8 * 540 + X ^ 9 * 725
def G9 : (ZMod 1249)[X] := 774 + X * 1070 + X ^ 2 * 484 + X ^ 3 * 1078 + X ^ 4 * 337 + X ^ 5 * 254 + X ^ 6 * 1020 + X ^ 7 * 43 + X ^ 8 * 1231 + X ^ 9 * 827
def G10 : (ZMod 1249)[X] := 751 + X * 909 + X ^ 2 * 757 + X ^ 3 * 1036 + X ^ 4 * 8 + X ^ 5 * 555 + X ^ 6 * 960 + X ^ 7 * 670 + X ^ 8 * 739 + X ^ 9 * 554
def G11 : (ZMod 1249)[X] := 428 + X * 709 + X ^ 2 * 609 + X ^ 3 * 662 + X ^ 4 * 938 + X ^ 5 * 580 + X ^ 6 * 353 + X ^ 7 * 437 + X ^ 8 * 600 + X ^ 9 * 484
def G12 : (ZMod 1249)[X] := 1237 + X * 739 + X ^ 3 * 373 + X ^ 4 * 478 + X ^ 5 * 931 + X ^ 6 * 675 + X ^ 7 * 828 + X ^ 8 * 883 + X ^ 9 * 283
def G13 : (ZMod 1249)[X] := 257 + X * 936 + X ^ 2 * 395 + X ^ 3 * 315 + X ^ 4 * 861 + X ^ 5 * 1105 + X ^ 6 * 489 + X ^ 7 * 281 + X ^ 8 * 3 + X ^ 9 * 166
def G14 : (ZMod 1249)[X] := 1122 + X * 816 + X ^ 2 * 776 + X ^ 3 * 761 + X ^ 4 * 503 + X ^ 5 * 828 + X ^ 6 * 994 + X ^ 7 * 215 + X ^ 8 * 593 + X ^ 9 * 415
def G15 : (ZMod 1249)[X] := 230 + X * 1206 + X ^ 2 * 552 + X ^ 3 * 902 + X ^ 4 * 330 + X ^ 5 * 697 + X ^ 6 * 63 + X ^ 7 * 268 + X ^ 8 * 1233 + X ^ 9 * 643
def G16 : (ZMod 1249)[X] := 332 + X * 356 + X ^ 2 * 385 + X ^ 3 * 69 + X ^ 4 * 1192 + X ^ 5 * 1182 + X ^ 6 * 95 + X ^ 7 * 872 + X ^ 8 * 294 + X ^ 9 * 773
def G17 : (ZMod 1249)[X] := 863 + X * 476 + X ^ 2 * 443 + X ^ 3 * 303 + X ^ 4 * 126 + X ^ 5 * 1109 + X ^ 6 * 537 + X ^ 7 * 855 + X ^ 8 * 1104 + X ^ 9 * 913
def G18 : (ZMod 1249)[X] := 934 + X * 1084 + X ^ 2 * 365 + X ^ 3 * 289 + X ^ 4 * 720 + X ^ 5 * 235 + X ^ 6 * 880 + X ^ 7 * 176 + X ^ 8 * 1017 + X ^ 9 * 428
def Lgstep0 : (ZMod 1249)[X] := 1089 + X * 636 + X ^ 2 * 36 + X ^ 3 * 740 + X ^ 4 * 299 + X ^ 5 * 50 + X ^ 6 * 102 + X ^ 7 * 648 + X ^ 8 * 709 + X ^ 9 * 1198 + X ^ 10 * 639 + X ^ 11 * 743 + X ^ 12 * 877 + X ^ 13 * 1012 + X ^ 14 * 410 + X ^ 15 * 474 + X ^ 16 * 834 + X ^ 17 * 527 + X ^ 18 * 77
def Mgstep0 : (ZMod 1249)[X] := 1089 + X * 636 + X ^ 2 * 36 + X ^ 3 * 740 + X ^ 4 * 299 + X ^ 5 * 50 + X ^ 6 * 102 + X ^ 7 * 648 + X ^ 8 * 709 + X ^ 9 * 1198 + X ^ 10 * 639 + X ^ 11 * 743 + X ^ 12 * 877 + X ^ 13 * 1012 + X ^ 14 * 410 + X ^ 15 * 474 + X ^ 16 * 834 + X ^ 17 * 527 + X ^ 18 * 77
theorem gstep0 : Lgstep0 = Mgstep0 := by
  have hL : Lgstep0.natDegree ≤ 18 := by unfold Lgstep0; compute_degree!
  have hR : Mgstep0.natDegree ≤ 18 := by unfold Mgstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep0, Mgstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep1 : (ZMod 1249)[X] := 992 + X * 433 + X ^ 2 * 464 + X ^ 3 * 294 + X ^ 4 * 471 + X ^ 5 * 119 + X ^ 6 * 540 + X ^ 7 * 967 + X ^ 8 * 771 + X ^ 9 * 665 + X ^ 10 * 33 + X ^ 11 * 304 + X ^ 12 * 989 + X ^ 13 * 1188 + X ^ 14 * 683 + X ^ 15 * 135 + X ^ 16 * 16 + X ^ 17 * 1109 + X ^ 18 * 13
def Mgstep1 : (ZMod 1249)[X] := 992 + X * 433 + X ^ 2 * 464 + X ^ 3 * 294 + X ^ 4 * 471 + X ^ 5 * 119 + X ^ 6 * 540 + X ^ 7 * 967 + X ^ 8 * 771 + X ^ 9 * 665 + X ^ 10 * 33 + X ^ 11 * 304 + X ^ 12 * 989 + X ^ 13 * 1188 + X ^ 14 * 683 + X ^ 15 * 135 + X ^ 16 * 16 + X ^ 17 * 1109 + X ^ 18 * 13
theorem gstep1 : Lgstep1 = Mgstep1 := by
  have hL : Lgstep1.natDegree ≤ 18 := by unfold Lgstep1; compute_degree!
  have hR : Mgstep1.natDegree ≤ 18 := by unfold Mgstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep1, Mgstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep2 : (ZMod 1249)[X] := 1243 + X * 430 + X ^ 2 * 6 + X ^ 3 * 1044 + X ^ 4 * 792 + X ^ 5 * 785 + X ^ 6 * 49 + X ^ 7 * 1079 + X ^ 8 * 432 + X ^ 9 * 712 + X ^ 10 * 733 + X ^ 11 * 925 + X ^ 12 * 11 + X ^ 13 * 975 + X ^ 14 * 329 + X ^ 15 * 70 + X ^ 16 * 1167 + X ^ 17 * 222 + X ^ 18 * 836
def Mgstep2 : (ZMod 1249)[X] := 1243 + X * 430 + X ^ 2 * 6 + X ^ 3 * 1044 + X ^ 4 * 792 + X ^ 5 * 785 + X ^ 6 * 49 + X ^ 7 * 1079 + X ^ 8 * 432 + X ^ 9 * 712 + X ^ 10 * 733 + X ^ 11 * 925 + X ^ 12 * 11 + X ^ 13 * 975 + X ^ 14 * 329 + X ^ 15 * 70 + X ^ 16 * 1167 + X ^ 17 * 222 + X ^ 18 * 836
theorem gstep2 : Lgstep2 = Mgstep2 := by
  have hL : Lgstep2.natDegree ≤ 18 := by unfold Lgstep2; compute_degree!
  have hR : Mgstep2.natDegree ≤ 18 := by unfold Mgstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep2, Mgstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep3 : (ZMod 1249)[X] := 857 + X * 1015 + X ^ 2 * 1088 + X ^ 3 * 859 + X ^ 4 * 368 + X ^ 5 * 344 + X ^ 6 * 1117 + X ^ 7 * 1116 + X ^ 8 * 144 + X ^ 9 * 411 + X ^ 10 * 565 + X ^ 11 * 1208 + X ^ 12 * 980 + X ^ 13 * 1144 + X ^ 14 * 504 + X ^ 15 * 199 + X ^ 16 * 408 + X ^ 17 * 629 + X ^ 18 * 992
def Mgstep3 : (ZMod 1249)[X] := 857 + X * 1015 + X ^ 2 * 1088 + X ^ 3 * 859 + X ^ 4 * 368 + X ^ 5 * 344 + X ^ 6 * 1117 + X ^ 7 * 1116 + X ^ 8 * 144 + X ^ 9 * 411 + X ^ 10 * 565 + X ^ 11 * 1208 + X ^ 12 * 980 + X ^ 13 * 1144 + X ^ 14 * 504 + X ^ 15 * 199 + X ^ 16 * 408 + X ^ 17 * 629 + X ^ 18 * 992
theorem gstep3 : Lgstep3 = Mgstep3 := by
  have hL : Lgstep3.natDegree ≤ 18 := by unfold Lgstep3; compute_degree!
  have hR : Mgstep3.natDegree ≤ 18 := by unfold Mgstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep3, Mgstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep4 : (ZMod 1249)[X] := 729 + X * 181 + X ^ 2 * 1065 + X ^ 3 * 983 + X ^ 4 * 916 + X ^ 5 * 552 + X ^ 6 * 159 + X ^ 7 * 305 + X ^ 8 * 453 + X ^ 9 * 416 + X ^ 10 * 263 + X ^ 11 * 673 + X ^ 12 * 631 + X ^ 13 * 685 + X ^ 14 * 762 + X ^ 15 * 1181 + X ^ 16 * 60 + X ^ 17 * 1017 + X ^ 18 * 1015
def Mgstep4 : (ZMod 1249)[X] := 729 + X * 181 + X ^ 2 * 1065 + X ^ 3 * 983 + X ^ 4 * 916 + X ^ 5 * 552 + X ^ 6 * 159 + X ^ 7 * 305 + X ^ 8 * 453 + X ^ 9 * 416 + X ^ 10 * 263 + X ^ 11 * 673 + X ^ 12 * 631 + X ^ 13 * 685 + X ^ 14 * 762 + X ^ 15 * 1181 + X ^ 16 * 60 + X ^ 17 * 1017 + X ^ 18 * 1015
theorem gstep4 : Lgstep4 = Mgstep4 := by
  have hL : Lgstep4.natDegree ≤ 18 := by unfold Lgstep4; compute_degree!
  have hR : Mgstep4.natDegree ≤ 18 := by unfold Mgstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep4, Mgstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep5 : (ZMod 1249)[X] := 292 + X * 410 + X ^ 2 * 1147 + X ^ 3 * 413 + X ^ 4 * 765 + X ^ 5 * 1079 + X ^ 6 * 447 + X ^ 7 * 276 + X ^ 8 * 892 + X ^ 9 * 794 + X ^ 10 * 654 + X ^ 11 * 610 + X ^ 12 * 1207 + X ^ 13 * 122 + X ^ 14 * 549 + X ^ 15 * 538 + X ^ 16 * 497 + X ^ 17 * 467 + X ^ 18 * 562
def Mgstep5 : (ZMod 1249)[X] := 292 + X * 410 + X ^ 2 * 1147 + X ^ 3 * 413 + X ^ 4 * 765 + X ^ 5 * 1079 + X ^ 6 * 447 + X ^ 7 * 276 + X ^ 8 * 892 + X ^ 9 * 794 + X ^ 10 * 654 + X ^ 11 * 610 + X ^ 12 * 1207 + X ^ 13 * 122 + X ^ 14 * 549 + X ^ 15 * 538 + X ^ 16 * 497 + X ^ 17 * 467 + X ^ 18 * 562
theorem gstep5 : Lgstep5 = Mgstep5 := by
  have hL : Lgstep5.natDegree ≤ 18 := by unfold Lgstep5; compute_degree!
  have hR : Mgstep5.natDegree ≤ 18 := by unfold Mgstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep5, Mgstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep6 : (ZMod 1249)[X] := 1058 + X * 493 + X ^ 2 * 990 + X ^ 3 * 1032 + X ^ 4 * 979 + X ^ 5 * 409 + X ^ 6 * 995 + X ^ 7 * 58 + X ^ 8 * 693 + X ^ 9 * 1035 + X ^ 10 * 584 + X ^ 11 * 1065 + X ^ 12 * 491 + X ^ 13 * 933 + X ^ 14 * 168 + X ^ 15 * 319 + X ^ 16 * 421 + X ^ 17 * 114 + X ^ 18 * 1004
def Mgstep6 : (ZMod 1249)[X] := 1058 + X * 493 + X ^ 2 * 990 + X ^ 3 * 1032 + X ^ 4 * 979 + X ^ 5 * 409 + X ^ 6 * 995 + X ^ 7 * 58 + X ^ 8 * 693 + X ^ 9 * 1035 + X ^ 10 * 584 + X ^ 11 * 1065 + X ^ 12 * 491 + X ^ 13 * 933 + X ^ 14 * 168 + X ^ 15 * 319 + X ^ 16 * 421 + X ^ 17 * 114 + X ^ 18 * 1004
theorem gstep6 : Lgstep6 = Mgstep6 := by
  have hL : Lgstep6.natDegree ≤ 18 := by unfold Lgstep6; compute_degree!
  have hR : Mgstep6.natDegree ≤ 18 := by unfold Mgstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep6, Mgstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep7 : (ZMod 1249)[X] := 1119 + X * 8 + X ^ 2 * 437 + X ^ 3 * 784 + X ^ 4 * 25 + X ^ 5 * 484 + X ^ 6 * 92 + X ^ 7 * 705 + X ^ 8 * 779 + X ^ 9 * 332 + X ^ 10 * 851 + X ^ 11 * 35 + X ^ 12 * 293 + X ^ 13 * 1095 + X ^ 14 * 703 + X ^ 15 * 1160 + X ^ 16 * 645 + X ^ 17 * 249 + X ^ 18 * 474
def Mgstep7 : (ZMod 1249)[X] := 1119 + X * 8 + X ^ 2 * 437 + X ^ 3 * 784 + X ^ 4 * 25 + X ^ 5 * 484 + X ^ 6 * 92 + X ^ 7 * 705 + X ^ 8 * 779 + X ^ 9 * 332 + X ^ 10 * 851 + X ^ 11 * 35 + X ^ 12 * 293 + X ^ 13 * 1095 + X ^ 14 * 703 + X ^ 15 * 1160 + X ^ 16 * 645 + X ^ 17 * 249 + X ^ 18 * 474
theorem gstep7 : Lgstep7 = Mgstep7 := by
  have hL : Lgstep7.natDegree ≤ 18 := by unfold Lgstep7; compute_degree!
  have hR : Mgstep7.natDegree ≤ 18 := by unfold Mgstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep7, Mgstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep8 : (ZMod 1249)[X] := 640 + X * 837 + X ^ 2 * 5 + X ^ 3 * 10 + X ^ 4 * 333 + X ^ 5 * 1045 + X ^ 6 * 1231 + X ^ 7 * 736 + X ^ 8 * 1135 + X ^ 9 * 440 + X ^ 10 * 1018 + X ^ 11 * 25 + X ^ 12 * 291 + X ^ 13 * 665 + X ^ 14 * 932 + X ^ 15 * 924 + X ^ 16 * 150 + X ^ 17 * 1126 + X ^ 18 * 1045
def Mgstep8 : (ZMod 1249)[X] := 640 + X * 837 + X ^ 2 * 5 + X ^ 3 * 10 + X ^ 4 * 333 + X ^ 5 * 1045 + X ^ 6 * 1231 + X ^ 7 * 736 + X ^ 8 * 1135 + X ^ 9 * 440 + X ^ 10 * 1018 + X ^ 11 * 25 + X ^ 12 * 291 + X ^ 13 * 665 + X ^ 14 * 932 + X ^ 15 * 924 + X ^ 16 * 150 + X ^ 17 * 1126 + X ^ 18 * 1045
theorem gstep8 : Lgstep8 = Mgstep8 := by
  have hL : Lgstep8.natDegree ≤ 18 := by unfold Lgstep8; compute_degree!
  have hR : Mgstep8.natDegree ≤ 18 := by unfold Mgstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep8, Mgstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep9 : (ZMod 1249)[X] := 805 + X * 186 + X ^ 2 * 648 + X ^ 3 * 419 + X ^ 4 * 304 + X ^ 5 * 853 + X ^ 6 * 1210 + X ^ 7 * 637 + X ^ 8 * 330 + X ^ 9 * 291 + X ^ 10 * 389 + X ^ 11 * 1167 + X ^ 12 * 392 + X ^ 13 * 233 + X ^ 14 * 553 + X ^ 15 * 631 + X ^ 16 * 253 + X ^ 17 * 204 + X ^ 18 * 726
def Mgstep9 : (ZMod 1249)[X] := 805 + X * 186 + X ^ 2 * 648 + X ^ 3 * 419 + X ^ 4 * 304 + X ^ 5 * 853 + X ^ 6 * 1210 + X ^ 7 * 637 + X ^ 8 * 330 + X ^ 9 * 291 + X ^ 10 * 389 + X ^ 11 * 1167 + X ^ 12 * 392 + X ^ 13 * 233 + X ^ 14 * 553 + X ^ 15 * 631 + X ^ 16 * 253 + X ^ 17 * 204 + X ^ 18 * 726
theorem gstep9 : Lgstep9 = Mgstep9 := by
  have hL : Lgstep9.natDegree ≤ 18 := by unfold Lgstep9; compute_degree!
  have hR : Mgstep9.natDegree ≤ 18 := by unfold Mgstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep9, Mgstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep10 : (ZMod 1249)[X] := 702 + X * 161 + X ^ 2 * 1116 + X ^ 3 * 895 + X ^ 4 * 489 + X ^ 5 * 1092 + X ^ 6 * 399 + X ^ 7 * 105 + X ^ 8 * 450 + X ^ 9 * 893 + X ^ 10 * 715 + X ^ 11 * 293 + X ^ 12 * 1023 + X ^ 13 * 997 + X ^ 14 * 957 + X ^ 15 * 584 + X ^ 16 * 762 + X ^ 17 * 717 + X ^ 18 * 911
def Mgstep10 : (ZMod 1249)[X] := 702 + X * 161 + X ^ 2 * 1116 + X ^ 3 * 895 + X ^ 4 * 489 + X ^ 5 * 1092 + X ^ 6 * 399 + X ^ 7 * 105 + X ^ 8 * 450 + X ^ 9 * 893 + X ^ 10 * 715 + X ^ 11 * 293 + X ^ 12 * 1023 + X ^ 13 * 997 + X ^ 14 * 957 + X ^ 15 * 584 + X ^ 16 * 762 + X ^ 17 * 717 + X ^ 18 * 911
theorem gstep10 : Lgstep10 = Mgstep10 := by
  have hL : Lgstep10.natDegree ≤ 18 := by unfold Lgstep10; compute_degree!
  have hR : Mgstep10.natDegree ≤ 18 := by unfold Mgstep10; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep10, Mgstep10, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep11 : (ZMod 1249)[X] := 830 + X * 1139 + X ^ 2 * 1054 + X ^ 3 * 129 + X ^ 4 * 466 + X ^ 5 * 1237 + X ^ 6 * 2 + X ^ 7 * 238 + X ^ 8 * 1054 + X ^ 9 * 506 + X ^ 10 * 475 + X ^ 11 * 296 + X ^ 12 * 1114 + X ^ 13 * 287 + X ^ 14 * 700 + X ^ 15 * 547 + X ^ 16 * 1142 + X ^ 17 * 15 + X ^ 18 * 693
def Mgstep11 : (ZMod 1249)[X] := 830 + X * 1139 + X ^ 2 * 1054 + X ^ 3 * 129 + X ^ 4 * 466 + X ^ 5 * 1237 + X ^ 6 * 2 + X ^ 7 * 238 + X ^ 8 * 1054 + X ^ 9 * 506 + X ^ 10 * 475 + X ^ 11 * 296 + X ^ 12 * 1114 + X ^ 13 * 287 + X ^ 14 * 700 + X ^ 15 * 547 + X ^ 16 * 1142 + X ^ 17 * 15 + X ^ 18 * 693
theorem gstep11 : Lgstep11 = Mgstep11 := by
  have hL : Lgstep11.natDegree ≤ 18 := by unfold Lgstep11; compute_degree!
  have hR : Mgstep11.natDegree ≤ 18 := by unfold Mgstep11; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep11, Mgstep11, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep12 : (ZMod 1249)[X] := 144 + X * 999 + X ^ 2 * 308 + X ^ 3 * 1040 + X ^ 4 * 254 + X ^ 5 * 937 + X ^ 6 * 147 + X ^ 7 * 434 + X ^ 8 * 1053 + X ^ 9 * 273 + X ^ 10 * 63 + X ^ 11 * 553 + X ^ 12 * 71 + X ^ 13 * 1171 + X ^ 14 * 255 + X ^ 15 * 774 + X ^ 16 * 586 + X ^ 17 * 178 + X ^ 18 * 153
def Mgstep12 : (ZMod 1249)[X] := 144 + X * 999 + X ^ 2 * 308 + X ^ 3 * 1040 + X ^ 4 * 254 + X ^ 5 * 937 + X ^ 6 * 147 + X ^ 7 * 434 + X ^ 8 * 1053 + X ^ 9 * 273 + X ^ 10 * 63 + X ^ 11 * 553 + X ^ 12 * 71 + X ^ 13 * 1171 + X ^ 14 * 255 + X ^ 15 * 774 + X ^ 16 * 586 + X ^ 17 * 178 + X ^ 18 * 153
theorem gstep12 : Lgstep12 = Mgstep12 := by
  have hL : Lgstep12.natDegree ≤ 18 := by unfold Lgstep12; compute_degree!
  have hR : Mgstep12.natDegree ≤ 18 := by unfold Mgstep12; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep12, Mgstep12, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep13 : (ZMod 1249)[X] := 1101 + X * 239 + X ^ 2 * 1239 + X ^ 3 * 821 + X ^ 4 * 460 + X ^ 5 * 556 + X ^ 6 * 552 + X ^ 7 * 953 + X ^ 8 * 737 + X ^ 9 * 830 + X ^ 10 * 279 + X ^ 11 * 211 + X ^ 12 * 653 + X ^ 13 * 254 + X ^ 14 * 364 + X ^ 15 * 415 + X ^ 16 * 875 + X ^ 17 * 996 + X ^ 18 * 78
def Mgstep13 : (ZMod 1249)[X] := 1101 + X * 239 + X ^ 2 * 1239 + X ^ 3 * 821 + X ^ 4 * 460 + X ^ 5 * 556 + X ^ 6 * 552 + X ^ 7 * 953 + X ^ 8 * 737 + X ^ 9 * 830 + X ^ 10 * 279 + X ^ 11 * 211 + X ^ 12 * 653 + X ^ 13 * 254 + X ^ 14 * 364 + X ^ 15 * 415 + X ^ 16 * 875 + X ^ 17 * 996 + X ^ 18 * 78
theorem gstep13 : Lgstep13 = Mgstep13 := by
  have hL : Lgstep13.natDegree ≤ 18 := by unfold Lgstep13; compute_degree!
  have hR : Mgstep13.natDegree ≤ 18 := by unfold Mgstep13; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep13, Mgstep13, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep14 : (ZMod 1249)[X] := 1141 + X * 70 + X ^ 2 * 377 + X ^ 3 * 247 + X ^ 4 * 240 + X ^ 5 * 590 + X ^ 6 * 565 + X ^ 7 * 1116 + X ^ 8 * 28 + X ^ 9 * 967 + X ^ 10 * 784 + X ^ 11 * 459 + X ^ 12 * 573 + X ^ 13 * 880 + X ^ 14 * 130 + X ^ 15 * 874 + X ^ 16 * 523 + X ^ 17 * 84 + X ^ 18 * 1112
def Mgstep14 : (ZMod 1249)[X] := 1141 + X * 70 + X ^ 2 * 377 + X ^ 3 * 247 + X ^ 4 * 240 + X ^ 5 * 590 + X ^ 6 * 565 + X ^ 7 * 1116 + X ^ 8 * 28 + X ^ 9 * 967 + X ^ 10 * 784 + X ^ 11 * 459 + X ^ 12 * 573 + X ^ 13 * 880 + X ^ 14 * 130 + X ^ 15 * 874 + X ^ 16 * 523 + X ^ 17 * 84 + X ^ 18 * 1112
theorem gstep14 : Lgstep14 = Mgstep14 := by
  have hL : Lgstep14.natDegree ≤ 18 := by unfold Lgstep14; compute_degree!
  have hR : Mgstep14.natDegree ≤ 18 := by unfold Mgstep14; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep14, Mgstep14, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep15 : (ZMod 1249)[X] := 442 + X * 204 + X ^ 2 * 973 + X ^ 3 * 242 + X ^ 4 * 485 + X ^ 5 * 329 + X ^ 6 * 380 + X ^ 7 * 107 + X ^ 8 * 307 + X ^ 9 * 134 + X ^ 10 * 1149 + X ^ 11 * 217 + X ^ 12 * 695 + X ^ 13 * 1192 + X ^ 14 * 673 + X ^ 16 * 180 + X ^ 17 * 657 + X ^ 18 * 30
def Mgstep15 : (ZMod 1249)[X] := 442 + X * 204 + X ^ 2 * 973 + X ^ 3 * 242 + X ^ 4 * 485 + X ^ 5 * 329 + X ^ 6 * 380 + X ^ 7 * 107 + X ^ 8 * 307 + X ^ 9 * 134 + X ^ 10 * 1149 + X ^ 11 * 217 + X ^ 12 * 695 + X ^ 13 * 1192 + X ^ 14 * 673 + X ^ 16 * 180 + X ^ 17 * 657 + X ^ 18 * 30
theorem gstep15 : Lgstep15 = Mgstep15 := by
  have hL : Lgstep15.natDegree ≤ 18 := by unfold Lgstep15; compute_degree!
  have hR : Mgstep15.natDegree ≤ 18 := by unfold Mgstep15; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep15, Mgstep15, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep16 : (ZMod 1249)[X] := 312 + X * 323 + X ^ 2 * 182 + X ^ 3 * 192 + X ^ 4 * 882 + X ^ 5 * 532 + X ^ 6 * 1227 + X ^ 7 * 162 + X ^ 8 * 190 + X ^ 9 * 920 + X ^ 10 * 214 + X ^ 11 * 313 + X ^ 12 * 307 + X ^ 13 * 692 + X ^ 14 * 732 + X ^ 15 * 134 + X ^ 16 * 696 + X ^ 17 * 1137 + X ^ 18 * 507
def Mgstep16 : (ZMod 1249)[X] := 312 + X * 323 + X ^ 2 * 182 + X ^ 3 * 192 + X ^ 4 * 882 + X ^ 5 * 532 + X ^ 6 * 1227 + X ^ 7 * 162 + X ^ 8 * 190 + X ^ 9 * 920 + X ^ 10 * 214 + X ^ 11 * 313 + X ^ 12 * 307 + X ^ 13 * 692 + X ^ 14 * 732 + X ^ 15 * 134 + X ^ 16 * 696 + X ^ 17 * 1137 + X ^ 18 * 507
theorem gstep16 : Lgstep16 = Mgstep16 := by
  have hL : Lgstep16.natDegree ≤ 18 := by unfold Lgstep16; compute_degree!
  have hR : Mgstep16.natDegree ≤ 18 := by unfold Mgstep16; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep16, Mgstep16, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lgstep17 : (ZMod 1249)[X] := 365 + X * 983 + X ^ 2 * 737 + X ^ 3 * 470 + X ^ 4 * 243 + X ^ 5 * 637 + X ^ 6 * 325 + X ^ 7 * 822 + X ^ 8 * 35 + X ^ 9 * 1209 + X ^ 10 * 1141 + X ^ 11 * 527 + X ^ 12 * 1159 + X ^ 13 * 1147 + X ^ 14 * 1160 + X ^ 15 * 698 + X ^ 16 * 1021 + X ^ 17 * 18 + X ^ 18 * 486
def Mgstep17 : (ZMod 1249)[X] := 365 + X * 983 + X ^ 2 * 737 + X ^ 3 * 470 + X ^ 4 * 243 + X ^ 5 * 637 + X ^ 6 * 325 + X ^ 7 * 822 + X ^ 8 * 35 + X ^ 9 * 1209 + X ^ 10 * 1141 + X ^ 11 * 527 + X ^ 12 * 1159 + X ^ 13 * 1147 + X ^ 14 * 1160 + X ^ 15 * 698 + X ^ 16 * 1021 + X ^ 17 * 18 + X ^ 18 * 486
theorem gstep17 : Lgstep17 = Mgstep17 := by
  have hL : Lgstep17.natDegree ≤ 18 := by unfold Lgstep17; compute_degree!
  have hR : Mgstep17.natDegree ≤ 18 := by unfold Mgstep17; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lgstep17, Mgstep17, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2566Batch7Actual

end