import tmp.sheaf.xif.paper.S2563Batch4Actual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2563Batch4Actual

namespace LeanFormal.IUT.XiFPaper.S2564Batch5Actual

def C0 : (ZMod 1249)[X] := 794 + X * 903 + X ^ 2 * 1242 + X ^ 3 * 100 + X ^ 4 * 526 + X ^ 5 * 715 + X ^ 6 * 798 + X ^ 7 * 237 + X ^ 8 * 993 + X ^ 9 * 685
def C1 : (ZMod 1249)[X] := 224 + X * 544 + X ^ 2 * 149 + X ^ 3 * 451 + X ^ 4 * 508 + X ^ 5 * 600 + X ^ 6 * 1216 + X ^ 7 * 283 + X ^ 8 * 347 + X ^ 9 * 478
def C2 : (ZMod 1249)[X] := 1144 + X * 350 + X ^ 2 * 590 + X ^ 3 * 873 + X ^ 4 * 1146 + X ^ 5 * 908 + X ^ 6 * 540 + X ^ 7 * 905 + X ^ 8 * 826 + X ^ 9 * 1245
def C3 : (ZMod 1249)[X] := 466 + X * 107 + X ^ 2 * 355 + X ^ 3 * 770 + X ^ 4 * 375 + X ^ 5 * 459 + X ^ 6 * 698 + X ^ 7 * 283 + X ^ 8 * 982 + X ^ 9 * 685
def C4 : (ZMod 1249)[X] := 762 + X * 335 + X ^ 2 * 659 + X ^ 3 * 508 + X ^ 4 * 66 + X ^ 5 * 796 + X ^ 6 * 770 + X ^ 7 * 670 + X ^ 8 * 293 + X ^ 9 * 881
def Lcstep0 : (ZMod 1249)[X] := 923 + X * 513 + X ^ 2 * 1123 + X ^ 3 * 158 + X ^ 4 * 663 + X ^ 5 * 874 + X ^ 6 * 168 + X ^ 7 * 187 + X ^ 8 * 695 + X ^ 9 * 558 + X ^ 10 * 237 + X ^ 11 * 7 + X ^ 12 * 320 + X ^ 13 * 290 + X ^ 14 * 934 + X ^ 15 * 228 + X ^ 16 * 581 + X ^ 17 * 676 + X ^ 18 * 1040
def Mcstep0 : (ZMod 1249)[X] := 923 + X * 513 + X ^ 2 * 1123 + X ^ 3 * 158 + X ^ 4 * 663 + X ^ 5 * 874 + X ^ 6 * 168 + X ^ 7 * 187 + X ^ 8 * 695 + X ^ 9 * 558 + X ^ 10 * 237 + X ^ 11 * 7 + X ^ 12 * 320 + X ^ 13 * 290 + X ^ 14 * 934 + X ^ 15 * 228 + X ^ 16 * 581 + X ^ 17 * 676 + X ^ 18 * 1040
theorem cstep0 : Lcstep0 = Mcstep0 := by
  have hL : Lcstep0.natDegree ≤ 18 := by unfold Lcstep0; compute_degree!
  have hR : Mcstep0.natDegree ≤ 18 := by unfold Mcstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lcstep0, Mcstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lcstep1 : (ZMod 1249)[X] := 557 + X * 405 + X ^ 2 * 542 + X ^ 3 * 1048 + X ^ 4 * 1173 + X ^ 5 * 790 + X ^ 6 * 1105 + X ^ 7 * 630 + X ^ 8 * 400 + X ^ 9 * 1037 + X ^ 10 * 70 + X ^ 11 * 465 + X ^ 12 * 1146 + X ^ 13 * 1111 + X ^ 14 * 1188 + X ^ 15 * 6 + X ^ 16 * 47 + X ^ 17 * 487 + X ^ 18 * 980
def Mcstep1 : (ZMod 1249)[X] := 557 + X * 405 + X ^ 2 * 542 + X ^ 3 * 1048 + X ^ 4 * 1173 + X ^ 5 * 790 + X ^ 6 * 1105 + X ^ 7 * 630 + X ^ 8 * 400 + X ^ 9 * 1037 + X ^ 10 * 70 + X ^ 11 * 465 + X ^ 12 * 1146 + X ^ 13 * 1111 + X ^ 14 * 1188 + X ^ 15 * 6 + X ^ 16 * 47 + X ^ 17 * 487 + X ^ 18 * 980
theorem cstep1 : Lcstep1 = Mcstep1 := by
  have hL : Lcstep1.natDegree ≤ 18 := by unfold Lcstep1; compute_degree!
  have hR : Mcstep1.natDegree ≤ 18 := by unfold Mcstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lcstep1, Mcstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lcstep2 : (ZMod 1249)[X] := 499 + X * 674 + X ^ 2 * 121 + X ^ 3 * 1200 + X ^ 4 * 900 + X ^ 5 * 489 + X ^ 6 * 580 + X ^ 7 * 534 + X ^ 8 * 385 + X ^ 9 * 662 + X ^ 10 * 668 + X ^ 11 * 521 + X ^ 12 * 820 + X ^ 13 * 893 + X ^ 14 * 136 + X ^ 15 * 1106 + X ^ 16 * 16 + X ^ 17 * 772 + X ^ 18 * 406
def Mcstep2 : (ZMod 1249)[X] := 499 + X * 674 + X ^ 2 * 121 + X ^ 3 * 1200 + X ^ 4 * 900 + X ^ 5 * 489 + X ^ 6 * 580 + X ^ 7 * 534 + X ^ 8 * 385 + X ^ 9 * 662 + X ^ 10 * 668 + X ^ 11 * 521 + X ^ 12 * 820 + X ^ 13 * 893 + X ^ 14 * 136 + X ^ 15 * 1106 + X ^ 16 * 16 + X ^ 17 * 772 + X ^ 18 * 406
theorem cstep2 : Lcstep2 = Mcstep2 := by
  have hL : Lcstep2.natDegree ≤ 18 := by unfold Lcstep2; compute_degree!
  have hR : Mcstep2.natDegree ≤ 18 := by unfold Mcstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lcstep2, Mcstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lcstep3 : (ZMod 1249)[X] := 413 + X * 693 + X ^ 2 * 458 + X ^ 3 * 163 + X ^ 4 * 920 + X ^ 5 * 296 + X ^ 6 * 1068 + X ^ 7 * 1095 + X ^ 8 * 1142 + X ^ 9 * 502 + X ^ 10 * 325 + X ^ 11 * 77 + X ^ 12 * 346 + X ^ 13 * 763 + X ^ 14 * 944 + X ^ 15 * 35 + X ^ 16 * 681 + X ^ 17 * 960 + X ^ 18 * 46
def Mcstep3 : (ZMod 1249)[X] := 413 + X * 693 + X ^ 2 * 458 + X ^ 3 * 163 + X ^ 4 * 920 + X ^ 5 * 296 + X ^ 6 * 1068 + X ^ 7 * 1095 + X ^ 8 * 1142 + X ^ 9 * 502 + X ^ 10 * 325 + X ^ 11 * 77 + X ^ 12 * 346 + X ^ 13 * 763 + X ^ 14 * 944 + X ^ 15 * 35 + X ^ 16 * 681 + X ^ 17 * 960 + X ^ 18 * 46
theorem cstep3 : Lcstep3 = Mcstep3 := by
  have hL : Lcstep3.natDegree ≤ 18 := by unfold Lcstep3; compute_degree!
  have hR : Mcstep3.natDegree ≤ 18 := by unfold Mcstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lcstep3, Mcstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def D0 : (ZMod 1249)[X] := 762 + X * 335 + X ^ 2 * 659 + X ^ 3 * 508 + X ^ 4 * 66 + X ^ 5 * 796 + X ^ 6 * 770 + X ^ 7 * 670 + X ^ 8 * 293 + X ^ 9 * 881
def D1 : (ZMod 1249)[X] := 882 + X * 954 + X ^ 2 * 79 + X ^ 3 * 1113 + X ^ 4 * 167 + X ^ 5 * 679 + X ^ 6 * 333 + X ^ 7 * 1036 + X ^ 8 * 1096 + X ^ 9 * 665
def D2 : (ZMod 1249)[X] := 894 + X * 1132 + X ^ 2 * 382 + X ^ 3 * 426 + X ^ 4 * 623 + X ^ 5 * 468 + X ^ 6 * 464 + X ^ 7 * 75 + X ^ 8 * 368 + X ^ 9 * 238
def D3 : (ZMod 1249)[X] := 713 + X * 1165 + X ^ 2 * 380 + X ^ 3 * 942 + X ^ 4 * 7 + X ^ 5 * 652 + X ^ 6 * 234 + X ^ 7 * 845 + X ^ 8 * 219 + X ^ 9 * 411
def D4 : (ZMod 1249)[X] := 366 + X * 1096 + X ^ 2 * 1209 + X ^ 3 * 1248 + X ^ 4 * 741 + X ^ 5 * 789 + X ^ 6 * 164 + X ^ 7 * 585 + X ^ 8 * 373 + X ^ 9 * 126
def D5 : (ZMod 1249)[X] := 374 + X * 975 + X ^ 2 * 97 + X ^ 3 * 269 + X ^ 4 * 381 + X ^ 5 * 788 + X ^ 6 * 349 + X ^ 7 * 966 + X ^ 8 * 1135 + X ^ 9 * 940
def D6 : (ZMod 1249)[X] := 449 + X * 1142 + X ^ 2 * 1059 + X ^ 3 * 418 + X ^ 4 * 206 + X ^ 5 * 302 + X ^ 6 * 477 + X ^ 7 * 1019 + X ^ 8 * 923 + X ^ 9 * 420
def D7 : (ZMod 1249)[X] := 342 + X * 295 + X ^ 2 * 534 + X ^ 3 * 317 + X ^ 4 * 1105 + X ^ 5 * 189 + X ^ 6 * 891 + X ^ 7 * 819 + X ^ 8 * 956 + X ^ 9 * 667
def D8 : (ZMod 1249)[X] := 896 + X * 17 + X ^ 2 * 668 + X ^ 3 * 660 + X ^ 4 * 472 + X ^ 5 * 352 + X ^ 6 * 863 + X ^ 7 * 404 + X ^ 8 * 356 + X ^ 9 * 1075
def D9 : (ZMod 1249)[X] := 124 + X * 415 + X ^ 2 * 501 + X ^ 3 * 562 + X ^ 4 * 686 + X ^ 5 * 348 + X ^ 6 * 1108 + X ^ 7 * 428 + X ^ 8 * 537 + X ^ 9 * 111
def D10 : (ZMod 1249)[X] := 1173 + X * 266 + X ^ 2 * 309 + X ^ 3 * 1199 + X ^ 4 * 260 + X ^ 5 * 457 + X ^ 6 * 906 + X ^ 7 * 116 + X ^ 8 * 548 + X ^ 9 * 571
def Ldstep0 : (ZMod 1249)[X] := 1108 + X * 948 + X ^ 2 * 1184 + X ^ 3 * 445 + X ^ 4 * 925 + X ^ 5 * 910 + X ^ 6 * 994 + X ^ 7 * 288 + X ^ 8 * 564 + X ^ 9 * 805 + X ^ 10 * 585 + X ^ 11 * 346 + X ^ 12 * 388 + X ^ 13 * 840 + X ^ 14 * 765 + X ^ 15 * 760 + X ^ 16 * 1152 + X ^ 17 * 429 + X ^ 18 * 532
def Mdstep0 : (ZMod 1249)[X] := 1108 + X * 948 + X ^ 2 * 1184 + X ^ 3 * 445 + X ^ 4 * 925 + X ^ 5 * 910 + X ^ 6 * 994 + X ^ 7 * 288 + X ^ 8 * 564 + X ^ 9 * 805 + X ^ 10 * 585 + X ^ 11 * 346 + X ^ 12 * 388 + X ^ 13 * 840 + X ^ 14 * 765 + X ^ 15 * 760 + X ^ 16 * 1152 + X ^ 17 * 429 + X ^ 18 * 532
theorem dstep0 : Ldstep0 = Mdstep0 := by
  have hL : Ldstep0.natDegree ≤ 18 := by unfold Ldstep0; compute_degree!
  have hR : Mdstep0.natDegree ≤ 18 := by unfold Mdstep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep0, Mdstep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep1 : (ZMod 1249)[X] := 1046 + X * 453 + X ^ 2 * 312 + X ^ 3 * 756 + X ^ 4 * 124 + X ^ 5 * 1100 + X ^ 6 * 619 + X ^ 7 * 497 + X ^ 8 * 144 + X ^ 9 * 729 + X ^ 10 * 96 + X ^ 11 * 680 + X ^ 12 * 574 + X ^ 13 * 1125 + X ^ 14 * 968 + X ^ 15 * 974 + X ^ 16 * 1160 + X ^ 17 * 97 + X ^ 18 * 79
def Mdstep1 : (ZMod 1249)[X] := 1046 + X * 453 + X ^ 2 * 312 + X ^ 3 * 756 + X ^ 4 * 124 + X ^ 5 * 1100 + X ^ 6 * 619 + X ^ 7 * 497 + X ^ 8 * 144 + X ^ 9 * 729 + X ^ 10 * 96 + X ^ 11 * 680 + X ^ 12 * 574 + X ^ 13 * 1125 + X ^ 14 * 968 + X ^ 15 * 974 + X ^ 16 * 1160 + X ^ 17 * 97 + X ^ 18 * 79
theorem dstep1 : Ldstep1 = Mdstep1 := by
  have hL : Ldstep1.natDegree ≤ 18 := by unfold Ldstep1; compute_degree!
  have hR : Mdstep1.natDegree ≤ 18 := by unfold Mdstep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep1, Mdstep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep2 : (ZMod 1249)[X] := 1125 + X * 636 + X ^ 2 * 1012 + X ^ 3 * 338 + X ^ 4 * 1092 + X ^ 5 * 1029 + X ^ 6 * 1170 + X ^ 7 * 853 + X ^ 8 * 721 + X ^ 9 * 39 + X ^ 10 * 1147 + X ^ 11 * 191 + X ^ 12 * 58 + X ^ 13 * 1164 + X ^ 14 * 353 + X ^ 15 * 35 + X ^ 16 * 11 + X ^ 17 * 308 + X ^ 18 * 439
def Mdstep2 : (ZMod 1249)[X] := 1125 + X * 636 + X ^ 2 * 1012 + X ^ 3 * 338 + X ^ 4 * 1092 + X ^ 5 * 1029 + X ^ 6 * 1170 + X ^ 7 * 853 + X ^ 8 * 721 + X ^ 9 * 39 + X ^ 10 * 1147 + X ^ 11 * 191 + X ^ 12 * 58 + X ^ 13 * 1164 + X ^ 14 * 353 + X ^ 15 * 35 + X ^ 16 * 11 + X ^ 17 * 308 + X ^ 18 * 439
theorem dstep2 : Ldstep2 = Mdstep2 := by
  have hL : Ldstep2.natDegree ≤ 18 := by unfold Ldstep2; compute_degree!
  have hR : Mdstep2.natDegree ≤ 18 := by unfold Mdstep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep2, Mdstep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep3 : (ZMod 1249)[X] := 26 + X * 120 + X ^ 2 * 625 + X ^ 3 * 476 + X ^ 4 * 1122 + X ^ 5 * 812 + X ^ 6 * 226 + X ^ 7 * 706 + X ^ 8 * 353 + X ^ 9 * 292 + X ^ 10 * 697 + X ^ 11 * 256 + X ^ 12 * 574 + X ^ 13 * 1089 + X ^ 14 * 1043 + X ^ 15 * 408 + X ^ 16 * 645 + X ^ 17 * 162 + X ^ 18 * 306
def Mdstep3 : (ZMod 1249)[X] := 26 + X * 120 + X ^ 2 * 625 + X ^ 3 * 476 + X ^ 4 * 1122 + X ^ 5 * 812 + X ^ 6 * 226 + X ^ 7 * 706 + X ^ 8 * 353 + X ^ 9 * 292 + X ^ 10 * 697 + X ^ 11 * 256 + X ^ 12 * 574 + X ^ 13 * 1089 + X ^ 14 * 1043 + X ^ 15 * 408 + X ^ 16 * 645 + X ^ 17 * 162 + X ^ 18 * 306
theorem dstep3 : Ldstep3 = Mdstep3 := by
  have hL : Ldstep3.natDegree ≤ 18 := by unfold Ldstep3; compute_degree!
  have hR : Mdstep3.natDegree ≤ 18 := by unfold Mdstep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep3, Mdstep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep4 : (ZMod 1249)[X] := 313 + X * 414 + X ^ 2 * 374 + X ^ 3 * 267 + X ^ 4 * 1003 + X ^ 5 * 1162 + X ^ 6 * 440 + X ^ 7 * 1184 + X ^ 8 * 162 + X ^ 9 * 1144 + X ^ 10 * 390 + X ^ 11 * 828 + X ^ 12 * 13 + X ^ 13 * 480 + X ^ 14 * 178 + X ^ 15 * 620 + X ^ 16 * 528 + X ^ 17 * 321 + X ^ 18 * 888
def Mdstep4 : (ZMod 1249)[X] := 313 + X * 414 + X ^ 2 * 374 + X ^ 3 * 267 + X ^ 4 * 1003 + X ^ 5 * 1162 + X ^ 6 * 440 + X ^ 7 * 1184 + X ^ 8 * 162 + X ^ 9 * 1144 + X ^ 10 * 390 + X ^ 11 * 828 + X ^ 12 * 13 + X ^ 13 * 480 + X ^ 14 * 178 + X ^ 15 * 620 + X ^ 16 * 528 + X ^ 17 * 321 + X ^ 18 * 888
theorem dstep4 : Ldstep4 = Mdstep4 := by
  have hL : Ldstep4.natDegree ≤ 18 := by unfold Ldstep4; compute_degree!
  have hR : Mdstep4.natDegree ≤ 18 := by unfold Mdstep4; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep4, Mdstep4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep5 : (ZMod 1249)[X] := 1237 + X * 1133 + X ^ 2 * 250 + X ^ 3 * 674 + X ^ 4 * 852 + X ^ 5 * 668 + X ^ 6 * 483 + X ^ 7 * 1127 + X ^ 8 * 938 + X ^ 9 * 108 + X ^ 10 * 50 + X ^ 11 * 770 + X ^ 12 * 970 + X ^ 13 * 603 + X ^ 14 * 643 + X ^ 15 * 1220 + X ^ 16 * 540 + X ^ 17 * 508 + X ^ 18 * 557
def Mdstep5 : (ZMod 1249)[X] := 1237 + X * 1133 + X ^ 2 * 250 + X ^ 3 * 674 + X ^ 4 * 852 + X ^ 5 * 668 + X ^ 6 * 483 + X ^ 7 * 1127 + X ^ 8 * 938 + X ^ 9 * 108 + X ^ 10 * 50 + X ^ 11 * 770 + X ^ 12 * 970 + X ^ 13 * 603 + X ^ 14 * 643 + X ^ 15 * 1220 + X ^ 16 * 540 + X ^ 17 * 508 + X ^ 18 * 557
theorem dstep5 : Ldstep5 = Mdstep5 := by
  have hL : Ldstep5.natDegree ≤ 18 := by unfold Ldstep5; compute_degree!
  have hR : Mdstep5.natDegree ≤ 18 := by unfold Mdstep5; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep5, Mdstep5, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep6 : (ZMod 1249)[X] := 512 + X * 87 + X ^ 2 * 701 + X ^ 3 * 107 + X ^ 4 * 491 + X ^ 5 * 826 + X ^ 6 * 530 + X ^ 7 * 1136 + X ^ 8 * 16 + X ^ 9 * 866 + X ^ 10 * 801 + X ^ 11 * 1020 + X ^ 12 * 661 + X ^ 13 * 271 + X ^ 14 * 572 + X ^ 15 * 1080 + X ^ 16 * 506 + X ^ 17 * 940 + X ^ 18 * 291
def Mdstep6 : (ZMod 1249)[X] := 512 + X * 87 + X ^ 2 * 701 + X ^ 3 * 107 + X ^ 4 * 491 + X ^ 5 * 826 + X ^ 6 * 530 + X ^ 7 * 1136 + X ^ 8 * 16 + X ^ 9 * 866 + X ^ 10 * 801 + X ^ 11 * 1020 + X ^ 12 * 661 + X ^ 13 * 271 + X ^ 14 * 572 + X ^ 15 * 1080 + X ^ 16 * 506 + X ^ 17 * 940 + X ^ 18 * 291
theorem dstep6 : Ldstep6 = Mdstep6 := by
  have hL : Ldstep6.natDegree ≤ 18 := by unfold Ldstep6; compute_degree!
  have hR : Mdstep6.natDegree ≤ 18 := by unfold Mdstep6; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep6, Mdstep6, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep7 : (ZMod 1249)[X] := 807 + X * 691 + X ^ 2 * 143 + X ^ 3 * 1063 + X ^ 4 * 239 + X ^ 5 * 678 + X ^ 6 * 685 + X ^ 7 * 1149 + X ^ 8 * 1048 + X ^ 9 * 1097 + X ^ 10 * 518 + X ^ 11 * 522 + X ^ 12 * 764 + X ^ 13 * 34 + X ^ 14 * 1081 + X ^ 15 * 477 + X ^ 16 * 588 + X ^ 17 * 75 + X ^ 18 * 245
def Mdstep7 : (ZMod 1249)[X] := 807 + X * 691 + X ^ 2 * 143 + X ^ 3 * 1063 + X ^ 4 * 239 + X ^ 5 * 678 + X ^ 6 * 685 + X ^ 7 * 1149 + X ^ 8 * 1048 + X ^ 9 * 1097 + X ^ 10 * 518 + X ^ 11 * 522 + X ^ 12 * 764 + X ^ 13 * 34 + X ^ 14 * 1081 + X ^ 15 * 477 + X ^ 16 * 588 + X ^ 17 * 75 + X ^ 18 * 245
theorem dstep7 : Ldstep7 = Mdstep7 := by
  have hL : Ldstep7.natDegree ≤ 18 := by unfold Ldstep7; compute_degree!
  have hR : Mdstep7.natDegree ≤ 18 := by unfold Mdstep7; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep7, Mdstep7, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep8 : (ZMod 1249)[X] := 958 + X * 488 + X ^ 2 * 803 + X ^ 3 * 147 + X ^ 4 * 540 + X ^ 5 * 1065 + X ^ 6 * 507 + X ^ 7 * 600 + X ^ 8 * 325 + X ^ 9 * 358 + X ^ 10 * 610 + X ^ 11 * 1115 + X ^ 12 * 228 + X ^ 13 * 549 + X ^ 14 * 700 + X ^ 15 * 1063 + X ^ 16 * 1132 + X ^ 17 * 1012 + X ^ 18 * 300
def Mdstep8 : (ZMod 1249)[X] := 958 + X * 488 + X ^ 2 * 803 + X ^ 3 * 147 + X ^ 4 * 540 + X ^ 5 * 1065 + X ^ 6 * 507 + X ^ 7 * 600 + X ^ 8 * 325 + X ^ 9 * 358 + X ^ 10 * 610 + X ^ 11 * 1115 + X ^ 12 * 228 + X ^ 13 * 549 + X ^ 14 * 700 + X ^ 15 * 1063 + X ^ 16 * 1132 + X ^ 17 * 1012 + X ^ 18 * 300
theorem dstep8 : Ldstep8 = Mdstep8 := by
  have hL : Ldstep8.natDegree ≤ 18 := by unfold Ldstep8; compute_degree!
  have hR : Mdstep8.natDegree ≤ 18 := by unfold Mdstep8; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep8, Mdstep8, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Ldstep9 : (ZMod 1249)[X] := 388 + X * 502 + X ^ 2 * 460 + X ^ 3 * 650 + X ^ 4 * 799 + X ^ 5 * 1033 + X ^ 6 * 594 + X ^ 7 * 1011 + X ^ 8 * 1099 + X ^ 9 * 793 + X ^ 10 * 1009 + X ^ 11 * 1103 + X ^ 12 * 241 + X ^ 13 * 672 + X ^ 14 * 343 + X ^ 15 * 1212 + X ^ 16 * 1191 + X ^ 17 * 559 + X ^ 18 * 1080
def Mdstep9 : (ZMod 1249)[X] := 388 + X * 502 + X ^ 2 * 460 + X ^ 3 * 650 + X ^ 4 * 799 + X ^ 5 * 1033 + X ^ 6 * 594 + X ^ 7 * 1011 + X ^ 8 * 1099 + X ^ 9 * 793 + X ^ 10 * 1009 + X ^ 11 * 1103 + X ^ 12 * 241 + X ^ 13 * 672 + X ^ 14 * 343 + X ^ 15 * 1212 + X ^ 16 * 1191 + X ^ 17 * 559 + X ^ 18 * 1080
theorem dstep9 : Ldstep9 = Mdstep9 := by
  have hL : Ldstep9.natDegree ≤ 18 := by unfold Ldstep9; compute_degree!
  have hR : Mdstep9.natDegree ≤ 18 := by unfold Mdstep9; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Ldstep9, Mdstep9, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def E0 : (ZMod 1249)[X] := 1173 + X * 266 + X ^ 2 * 309 + X ^ 3 * 1199 + X ^ 4 * 260 + X ^ 5 * 457 + X ^ 6 * 906 + X ^ 7 * 116 + X ^ 8 * 548 + X ^ 9 * 571
def E1 : (ZMod 1249)[X] := 1232 + X * 233 + X ^ 2 * 46 + X ^ 3 * 766 + X ^ 4 * 460 + X ^ 5 * 118 + X ^ 6 * 1175 + X ^ 7 * 1002 + X ^ 8 * 202 + X ^ 9 * 723
def E2 : (ZMod 1249)[X] := 188 + X * 283 + X ^ 2 * 412 + X ^ 3 * 79 + X ^ 4 * 561 + X ^ 5 * 808 + X ^ 6 * 677 + X ^ 7 * 698 + X ^ 8 * 975 + X ^ 9 * 202
def E3 : (ZMod 1249)[X] := 1165 + X * 317 + X ^ 2 * 1042 + X ^ 3 * 593 + X ^ 4 * 1167 + X ^ 5 * 1164 + X ^ 6 * 313 + X ^ 7 * 970 + X ^ 8 * 89 + X ^ 9 * 1069
def E4 : (ZMod 1249)[X] := 1194 + X * 810 + X ^ 2 * 856 + X ^ 3 * 203 + X ^ 4 * 881 + X ^ 5 * 314 + X ^ 6 * 738 + X ^ 7 * 1237 + X ^ 8 * 176 + X ^ 9 * 1189
def Lestep0 : (ZMod 1249)[X] := 237 + X * 1106 + X ^ 2 * 1178 + X ^ 3 * 910 + X ^ 4 * 959 + X ^ 5 * 530 + X ^ 6 * 1123 + X ^ 7 * 712 + X ^ 8 * 1165 + X ^ 9 * 1176 + X ^ 10 * 688 + X ^ 11 * 220 + X ^ 12 * 725 + X ^ 13 * 712 + X ^ 14 * 1136 + X ^ 15 * 360 + X ^ 16 * 1014 + X ^ 17 * 871 + X ^ 18 * 1161
def Mestep0 : (ZMod 1249)[X] := 237 + X * 1106 + X ^ 2 * 1178 + X ^ 3 * 910 + X ^ 4 * 959 + X ^ 5 * 530 + X ^ 6 * 1123 + X ^ 7 * 712 + X ^ 8 * 1165 + X ^ 9 * 1176 + X ^ 10 * 688 + X ^ 11 * 220 + X ^ 12 * 725 + X ^ 13 * 712 + X ^ 14 * 1136 + X ^ 15 * 360 + X ^ 16 * 1014 + X ^ 17 * 871 + X ^ 18 * 1161
theorem estep0 : Lestep0 = Mestep0 := by
  have hL : Lestep0.natDegree ≤ 18 := by unfold Lestep0; compute_degree!
  have hR : Mestep0.natDegree ≤ 18 := by unfold Mestep0; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lestep0, Mestep0, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lestep1 : (ZMod 1249)[X] := 1110 + X * 271 + X ^ 2 * 202 + X ^ 3 * 366 + X ^ 4 * 1147 + X ^ 5 * 250 + X ^ 6 * 126 + X ^ 7 * 147 + X ^ 8 * 881 + X ^ 9 * 796 + X ^ 10 * 1200 + X ^ 11 * 1100 + X ^ 12 * 107 + X ^ 13 * 336 + X ^ 14 * 550 + X ^ 15 * 631 + X ^ 16 * 99 + X ^ 17 * 271 + X ^ 18 * 153
def Mestep1 : (ZMod 1249)[X] := 1110 + X * 271 + X ^ 2 * 202 + X ^ 3 * 366 + X ^ 4 * 1147 + X ^ 5 * 250 + X ^ 6 * 126 + X ^ 7 * 147 + X ^ 8 * 881 + X ^ 9 * 796 + X ^ 10 * 1200 + X ^ 11 * 1100 + X ^ 12 * 107 + X ^ 13 * 336 + X ^ 14 * 550 + X ^ 15 * 631 + X ^ 16 * 99 + X ^ 17 * 271 + X ^ 18 * 153
theorem estep1 : Lestep1 = Mestep1 := by
  have hL : Lestep1.natDegree ≤ 18 := by unfold Lestep1; compute_degree!
  have hR : Mestep1.natDegree ≤ 18 := by unfold Mestep1; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lestep1, Mestep1, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lestep2 : (ZMod 1249)[X] := 368 + X * 623 + X ^ 2 * 1107 + X ^ 3 * 926 + X ^ 4 * 1187 + X ^ 5 * 854 + X ^ 6 * 1004 + X ^ 7 * 721 + X ^ 8 * 299 + X ^ 9 * 507 + X ^ 10 * 326 + X ^ 11 * 303 + X ^ 12 * 797 + X ^ 13 * 1067 + X ^ 14 * 47 + X ^ 15 * 412 + X ^ 16 * 694 + X ^ 17 * 437 + X ^ 18 * 32
def Mestep2 : (ZMod 1249)[X] := 368 + X * 623 + X ^ 2 * 1107 + X ^ 3 * 926 + X ^ 4 * 1187 + X ^ 5 * 854 + X ^ 6 * 1004 + X ^ 7 * 721 + X ^ 8 * 299 + X ^ 9 * 507 + X ^ 10 * 326 + X ^ 11 * 303 + X ^ 12 * 797 + X ^ 13 * 1067 + X ^ 14 * 47 + X ^ 15 * 412 + X ^ 16 * 694 + X ^ 17 * 437 + X ^ 18 * 32
theorem estep2 : Lestep2 = Mestep2 := by
  have hL : Lestep2.natDegree ≤ 18 := by unfold Lestep2; compute_degree!
  have hR : Mestep2.natDegree ≤ 18 := by unfold Mestep2; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lestep2, Mestep2, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Lestep3 : (ZMod 1249)[X] := 940 + X * 1084 + X ^ 2 * 519 + X ^ 3 * 441 + X ^ 4 * 374 + X ^ 5 * 67 + X ^ 6 * 482 + X ^ 7 * 397 + X ^ 8 * 450 + X ^ 9 * 70 + X ^ 10 * 203 + X ^ 11 * 840 + X ^ 12 * 117 + X ^ 13 * 412 + X ^ 14 * 1197 + X ^ 15 * 128 + X ^ 16 * 655 + X ^ 17 * 689 + X ^ 18 * 43
def Mestep3 : (ZMod 1249)[X] := 940 + X * 1084 + X ^ 2 * 519 + X ^ 3 * 441 + X ^ 4 * 374 + X ^ 5 * 67 + X ^ 6 * 482 + X ^ 7 * 397 + X ^ 8 * 450 + X ^ 9 * 70 + X ^ 10 * 203 + X ^ 11 * 840 + X ^ 12 * 117 + X ^ 13 * 412 + X ^ 14 * 1197 + X ^ 15 * 128 + X ^ 16 * 655 + X ^ 17 * 689 + X ^ 18 * 43
theorem estep3 : Lestep3 = Mestep3 := by
  have hL : Lestep3.natDegree ≤ 18 := by unfold Lestep3; compute_degree!
  have hR : Mestep3.natDegree ≤ 18 := by unfold Mestep3; compute_degree!
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Lestep3, Mestep3, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2564Batch5Actual

end