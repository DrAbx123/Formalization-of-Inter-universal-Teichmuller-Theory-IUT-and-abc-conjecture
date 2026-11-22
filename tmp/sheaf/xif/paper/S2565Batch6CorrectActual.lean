import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2565Batch6CorrectActual

def G0 : (ZMod 1249)[X] := C 1194 + C 810 * X + C 856 * X ^ 2 + C 203 * X ^ 3 + C 881 * X ^ 4 + C 314 * X ^ 5 + C 738 * X ^ 6 + C 1237 * X ^ 7 + C 176 * X ^ 8 + C 1189 * X ^ 9
def G1 : (ZMod 1249)[X] := C 626 + C 171 * X + C 845 * X ^ 2 + C 75 * X ^ 3 + C 1087 * X ^ 4 + C 774 * X ^ 5 + C 366 * X ^ 6 + C 846 * X ^ 7 + C 661 * X ^ 8 + C 47 * X ^ 9
def G2 : (ZMod 1249)[X] := C 223 + C 447 * X + C 1199 * X ^ 2 + C 1197 * X ^ 3 + C 702 * X ^ 4 + C 831 * X ^ 5 + C 1140 * X ^ 6 + C 1056 * X ^ 7 + C 1219 * X ^ 8 + C 170 * X ^ 9
def G3 : (ZMod 1249)[X] := C 922 + C 420 * X + C 897 * X ^ 2 + C 1062 * X ^ 3 + C 291 * X ^ 4 + C 556 * X ^ 5 + C 184 * X ^ 6 + C 25 * X ^ 7 + C 364 * X ^ 8 + C 261 * X ^ 9
def G4 : (ZMod 1249)[X] := C 155 + C 74 * X + C 323 * X ^ 2 + C 371 * X ^ 3 + C 198 * X ^ 4 + C 656 * X ^ 5 + C 372 * X ^ 6 + C 117 * X ^ 7 + C 861 * X ^ 8 + C 690 * X ^ 9
def G5 : (ZMod 1249)[X] := C 238 + C 329 * X + C 498 * X ^ 2 + C 782 * X ^ 3 + C 1092 * X ^ 4 + C 1061 * X ^ 5 + C 453 * X ^ 6 + C 472 * X ^ 7 + C 922 * X ^ 8 + C 770 * X ^ 9
def G6 : (ZMod 1249)[X] := C 495 + C 151 * X + C 112 * X ^ 2 + C 865 * X ^ 3 + C 1200 * X ^ 4 + C 441 * X ^ 5 + C 733 * X ^ 6 + C 1067 * X ^ 7 + C 449 * X ^ 8 + C 793 * X ^ 9
def G7 : (ZMod 1249)[X] := C 866 + C 826 * X + C 502 * X ^ 2 + C 1063 * X ^ 3 + C 149 * X ^ 4 + C 167 * X ^ 5 + C 323 * X ^ 6 + C 1184 * X ^ 7 + C 996 * X ^ 8 + C 63 * X ^ 9
def G8 : (ZMod 1249)[X] := C 66 + C 1144 * X + C 541 * X ^ 2 + C 701 * X ^ 3 + C 901 * X ^ 4 + C 1071 * X ^ 5 + C 321 * X ^ 6 + C 128 * X ^ 7 + C 1221 * X ^ 8 + C 131 * X ^ 9
def G9 : (ZMod 1249)[X] := C 830 + C 943 * X + C 219 * X ^ 2 + C 354 * X ^ 3 + C 89 * X ^ 4 + C 758 * X ^ 5 + C 900 * X ^ 6 + C 1166 * X ^ 7 + C 1063 * X ^ 8 + C 694 * X ^ 9
def G10 : (ZMod 1249)[X] := C 357 + C 445 * X + C 737 * X ^ 2 + C 242 * X ^ 3 + C 1004 * X ^ 4 + C 1090 * X ^ 5 + C 679 * X ^ 6 + C 975 * X ^ 7 + C 711 * X ^ 8 + C 1014 * X ^ 9
def G11 : (ZMod 1249)[X] := C 279 + C 392 * X + C 482 * X ^ 2 + C 1145 * X ^ 3 + C 783 * X ^ 4 + C 1187 * X ^ 5 + C 1137 * X ^ 6 + C 448 * X ^ 7 + C 891 * X ^ 8 + C 365 * X ^ 9
def G12 : (ZMod 1249)[X] := C 738 + C 273 * X + C 578 * X ^ 2 + C 928 * X ^ 3 + C 1090 * X ^ 4 + C 663 * X ^ 5 + C 483 * X ^ 6 + C 1181 * X ^ 7 + C 503 * X ^ 8 + C 166 * X ^ 9
def G13 : (ZMod 1249)[X] := C 994 + C 437 * X + C 1108 * X ^ 2 + C 59 * X ^ 3 + C 373 * X ^ 4 + C 392 * X ^ 5 + C 805 * X ^ 6 + C 204 * X ^ 7 + C 599 * X ^ 8 + C 240 * X ^ 9
def G14 : (ZMod 1249)[X] := C 1208 + C 1151 * X + C 1057 * X ^ 2 + C 645 * X ^ 3 + C 407 * X ^ 4 + C 114 * X ^ 5 + C 918 * X ^ 6 + C 746 * X ^ 7 + C 998 * X ^ 8 + C 1067 * X ^ 9
def G15 : (ZMod 1249)[X] := C 176 + C 1090 * X + C 313 * X ^ 2 + C 922 * X ^ 3 + C 830 * X ^ 4 + C 174 * X ^ 5 + C 85 * X ^ 6 + C 733 * X ^ 7 + C 997 * X ^ 8 + C 781 * X ^ 9
def G16 : (ZMod 1249)[X] := C 1085 + C 754 * X + C 95 * X ^ 2 + C 390 * X ^ 3 + C 888 * X ^ 4 + C 1009 * X ^ 5 + C 513 * X ^ 6 + C 642 * X ^ 7 + C 266 * X ^ 8 + C 447 * X ^ 9
def G17 : (ZMod 1249)[X] := C 1094 + C 912 * X + C 1121 * X ^ 2 + C 387 * X ^ 3 + C 145 * X ^ 4 + C 1211 * X ^ 5 + C 291 * X ^ 6 + C 672 * X ^ 7 + C 1142 * X ^ 8 + C 978 * X ^ 9
def G18 : (ZMod 1249)[X] := C 1216 + C 331 * X + C 278 * X ^ 2 + C 582 * X ^ 3 + C 778 * X ^ 4 + C 897 * X ^ 5 + C 168 * X ^ 6 + C 698 * X ^ 7 + C 790 * X ^ 8 + C 994 * X ^ 9
def Agstep0 : (ZMod 1249)[X] := C 1194 + C 810 * X + C 856 * X ^ 2 + C 203 * X ^ 3 + C 881 * X ^ 4 + C 314 * X ^ 5 + C 738 * X ^ 6 + C 1237 * X ^ 7 + C 176 * X ^ 8 + C 1189 * X ^ 9
def Bgstep0 : (ZMod 1249)[X] := C 1194 + C 810 * X + C 856 * X ^ 2 + C 203 * X ^ 3 + C 881 * X ^ 4 + C 314 * X ^ 5 + C 738 * X ^ 6 + C 1237 * X ^ 7 + C 176 * X ^ 8 + C 1189 * X ^ 9
def Qgstep0 : (ZMod 1249)[X] := C 325 + C 117 * X + C 735 * X ^ 2 + C 106 * X ^ 3 + C 235 * X ^ 4 + C 265 * X ^ 5 + C 886 * X ^ 6 + C 220 * X ^ 7 + C 1102 * X ^ 8
def Ngstep0 : (ZMod 1249)[X] := C 626 + C 171 * X + C 845 * X ^ 2 + C 75 * X ^ 3 + C 1087 * X ^ 4 + C 774 * X ^ 5 + C 366 * X ^ 6 + C 846 * X ^ 7 + C 661 * X ^ 8 + C 47 * X ^ 9
theorem gstep0 : Agstep0 * Bgstep0 = S2550F10 * Qgstep0 + Ngstep0 := by
  have hA : Agstep0.natDegree ≤ 9 := by unfold Agstep0; compute_degree!
  have hB : Bgstep0.natDegree ≤ 9 := by unfold Bgstep0; compute_degree!
  have hQ : Qgstep0.natDegree ≤ 8 := by unfold Qgstep0; compute_degree!
  have hN : Ngstep0.natDegree ≤ 9 := by unfold Ngstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep0 * Bgstep0).natDegree ≤ 18 := by
    calc (Agstep0 * Bgstep0).natDegree ≤ Agstep0.natDegree + Bgstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep0).natDegree ≤ S2550F10.natDegree + Qgstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep0 + Ngstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep0 + Ngstep0).natDegree
        ≤ max (S2550F10 * Qgstep0).natDegree Ngstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep0, Bgstep0, Qgstep0, Ngstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep1 : (ZMod 1249)[X] := C 626 + C 171 * X + C 845 * X ^ 2 + C 75 * X ^ 3 + C 1087 * X ^ 4 + C 774 * X ^ 5 + C 366 * X ^ 6 + C 846 * X ^ 7 + C 661 * X ^ 8 + C 47 * X ^ 9
def Bgstep1 : (ZMod 1249)[X] := C 626 + C 171 * X + C 845 * X ^ 2 + C 75 * X ^ 3 + C 1087 * X ^ 4 + C 774 * X ^ 5 + C 366 * X ^ 6 + C 846 * X ^ 7 + C 661 * X ^ 8 + C 47 * X ^ 9
def Qgstep1 : (ZMod 1249)[X] := C 854 + C 1009 * X + C 402 * X ^ 2 + C 9 * X ^ 3 + C 1043 * X ^ 4 + C 919 * X ^ 5 + C 897 * X ^ 6 + C 795 * X ^ 7 + C 960 * X ^ 8
def Ngstep1 : (ZMod 1249)[X] := C 223 + C 447 * X + C 1199 * X ^ 2 + C 1197 * X ^ 3 + C 702 * X ^ 4 + C 831 * X ^ 5 + C 1140 * X ^ 6 + C 1056 * X ^ 7 + C 1219 * X ^ 8 + C 170 * X ^ 9
theorem gstep1 : Agstep1 * Bgstep1 = S2550F10 * Qgstep1 + Ngstep1 := by
  have hA : Agstep1.natDegree ≤ 9 := by unfold Agstep1; compute_degree!
  have hB : Bgstep1.natDegree ≤ 9 := by unfold Bgstep1; compute_degree!
  have hQ : Qgstep1.natDegree ≤ 8 := by unfold Qgstep1; compute_degree!
  have hN : Ngstep1.natDegree ≤ 9 := by unfold Ngstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep1 * Bgstep1).natDegree ≤ 18 := by
    calc (Agstep1 * Bgstep1).natDegree ≤ Agstep1.natDegree + Bgstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep1).natDegree ≤ S2550F10.natDegree + Qgstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep1 + Ngstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep1 + Ngstep1).natDegree
        ≤ max (S2550F10 * Qgstep1).natDegree Ngstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep1, Bgstep1, Qgstep1, Ngstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep2 : (ZMod 1249)[X] := C 223 + C 447 * X + C 1199 * X ^ 2 + C 1197 * X ^ 3 + C 702 * X ^ 4 + C 831 * X ^ 5 + C 1140 * X ^ 6 + C 1056 * X ^ 7 + C 1219 * X ^ 8 + C 170 * X ^ 9
def Bgstep2 : (ZMod 1249)[X] := C 223 + C 447 * X + C 1199 * X ^ 2 + C 1197 * X ^ 3 + C 702 * X ^ 4 + C 831 * X ^ 5 + C 1140 * X ^ 6 + C 1056 * X ^ 7 + C 1219 * X ^ 8 + C 170 * X ^ 9
def Qgstep2 : (ZMod 1249)[X] := C 896 + C 1047 * X + C 497 * X ^ 2 + C 611 * X ^ 3 + C 371 * X ^ 4 + C 951 * X ^ 5 + C 131 * X ^ 6 + C 1102 * X ^ 7 + C 173 * X ^ 8
def Ngstep2 : (ZMod 1249)[X] := C 922 + C 420 * X + C 897 * X ^ 2 + C 1062 * X ^ 3 + C 291 * X ^ 4 + C 556 * X ^ 5 + C 184 * X ^ 6 + C 25 * X ^ 7 + C 364 * X ^ 8 + C 261 * X ^ 9
theorem gstep2 : Agstep2 * Bgstep2 = S2550F10 * Qgstep2 + Ngstep2 := by
  have hA : Agstep2.natDegree ≤ 9 := by unfold Agstep2; compute_degree!
  have hB : Bgstep2.natDegree ≤ 9 := by unfold Bgstep2; compute_degree!
  have hQ : Qgstep2.natDegree ≤ 8 := by unfold Qgstep2; compute_degree!
  have hN : Ngstep2.natDegree ≤ 9 := by unfold Ngstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep2 * Bgstep2).natDegree ≤ 18 := by
    calc (Agstep2 * Bgstep2).natDegree ≤ Agstep2.natDegree + Bgstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep2).natDegree ≤ S2550F10.natDegree + Qgstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep2 + Ngstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep2 + Ngstep2).natDegree
        ≤ max (S2550F10 * Qgstep2).natDegree Ngstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep2, Bgstep2, Qgstep2, Ngstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep3 : (ZMod 1249)[X] := C 922 + C 420 * X + C 897 * X ^ 2 + C 1062 * X ^ 3 + C 291 * X ^ 4 + C 556 * X ^ 5 + C 184 * X ^ 6 + C 25 * X ^ 7 + C 364 * X ^ 8 + C 261 * X ^ 9
def Bgstep3 : (ZMod 1249)[X] := C 922 + C 420 * X + C 897 * X ^ 2 + C 1062 * X ^ 3 + C 291 * X ^ 4 + C 556 * X ^ 5 + C 184 * X ^ 6 + C 25 * X ^ 7 + C 364 * X ^ 8 + C 261 * X ^ 9
def Qgstep3 : (ZMod 1249)[X] := C 688 + C 531 * X + C 1120 * X ^ 2 + C 966 * X ^ 3 + C 447 * X ^ 4 + C 275 * X ^ 5 + C 559 * X ^ 6 + C 102 * X ^ 7 + C 675 * X ^ 8
def Ngstep3 : (ZMod 1249)[X] := C 155 + C 74 * X + C 323 * X ^ 2 + C 371 * X ^ 3 + C 198 * X ^ 4 + C 656 * X ^ 5 + C 372 * X ^ 6 + C 117 * X ^ 7 + C 861 * X ^ 8 + C 690 * X ^ 9
theorem gstep3 : Agstep3 * Bgstep3 = S2550F10 * Qgstep3 + Ngstep3 := by
  have hA : Agstep3.natDegree ≤ 9 := by unfold Agstep3; compute_degree!
  have hB : Bgstep3.natDegree ≤ 9 := by unfold Bgstep3; compute_degree!
  have hQ : Qgstep3.natDegree ≤ 8 := by unfold Qgstep3; compute_degree!
  have hN : Ngstep3.natDegree ≤ 9 := by unfold Ngstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep3 * Bgstep3).natDegree ≤ 18 := by
    calc (Agstep3 * Bgstep3).natDegree ≤ Agstep3.natDegree + Bgstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep3).natDegree ≤ S2550F10.natDegree + Qgstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep3 + Ngstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep3 + Ngstep3).natDegree
        ≤ max (S2550F10 * Qgstep3).natDegree Ngstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep3, Bgstep3, Qgstep3, Ngstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep4 : (ZMod 1249)[X] := C 155 + C 74 * X + C 323 * X ^ 2 + C 371 * X ^ 3 + C 198 * X ^ 4 + C 656 * X ^ 5 + C 372 * X ^ 6 + C 117 * X ^ 7 + C 861 * X ^ 8 + C 690 * X ^ 9
def Bgstep4 : (ZMod 1249)[X] := C 155 + C 74 * X + C 323 * X ^ 2 + C 371 * X ^ 3 + C 198 * X ^ 4 + C 656 * X ^ 5 + C 372 * X ^ 6 + C 117 * X ^ 7 + C 861 * X ^ 8 + C 690 * X ^ 9
def Qgstep4 : (ZMod 1249)[X] := C 939 + C 216 * X + C 147 * X ^ 2 + C 1179 * X ^ 3 + C 710 * X ^ 4 + C 726 * X ^ 5 + C 521 * X ^ 6 + C 1105 * X ^ 7 + C 231 * X ^ 8
def Ngstep4 : (ZMod 1249)[X] := C 238 + C 329 * X + C 498 * X ^ 2 + C 782 * X ^ 3 + C 1092 * X ^ 4 + C 1061 * X ^ 5 + C 453 * X ^ 6 + C 472 * X ^ 7 + C 922 * X ^ 8 + C 770 * X ^ 9
theorem gstep4 : Agstep4 * Bgstep4 = S2550F10 * Qgstep4 + Ngstep4 := by
  have hA : Agstep4.natDegree ≤ 9 := by unfold Agstep4; compute_degree!
  have hB : Bgstep4.natDegree ≤ 9 := by unfold Bgstep4; compute_degree!
  have hQ : Qgstep4.natDegree ≤ 8 := by unfold Qgstep4; compute_degree!
  have hN : Ngstep4.natDegree ≤ 9 := by unfold Ngstep4; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep4 * Bgstep4).natDegree ≤ 18 := by
    calc (Agstep4 * Bgstep4).natDegree ≤ Agstep4.natDegree + Bgstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep4).natDegree ≤ S2550F10.natDegree + Qgstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep4 + Ngstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep4 + Ngstep4).natDegree
        ≤ max (S2550F10 * Qgstep4).natDegree Ngstep4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep4, Bgstep4, Qgstep4, Ngstep4, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep5 : (ZMod 1249)[X] := C 238 + C 329 * X + C 498 * X ^ 2 + C 782 * X ^ 3 + C 1092 * X ^ 4 + C 1061 * X ^ 5 + C 453 * X ^ 6 + C 472 * X ^ 7 + C 922 * X ^ 8 + C 770 * X ^ 9
def Bgstep5 : (ZMod 1249)[X] := C 238 + C 329 * X + C 498 * X ^ 2 + C 782 * X ^ 3 + C 1092 * X ^ 4 + C 1061 * X ^ 5 + C 453 * X ^ 6 + C 472 * X ^ 7 + C 922 * X ^ 8 + C 770 * X ^ 9
def Qgstep5 : (ZMod 1249)[X] := C 310 + C 1135 * X + C 219 * X ^ 2 + C 188 * X ^ 3 + C 915 * X ^ 4 + C 916 * X ^ 5 + C 215 * X ^ 6 + C 1187 * X ^ 7 + C 874 * X ^ 8
def Ngstep5 : (ZMod 1249)[X] := C 495 + C 151 * X + C 112 * X ^ 2 + C 865 * X ^ 3 + C 1200 * X ^ 4 + C 441 * X ^ 5 + C 733 * X ^ 6 + C 1067 * X ^ 7 + C 449 * X ^ 8 + C 793 * X ^ 9
theorem gstep5 : Agstep5 * Bgstep5 = S2550F10 * Qgstep5 + Ngstep5 := by
  have hA : Agstep5.natDegree ≤ 9 := by unfold Agstep5; compute_degree!
  have hB : Bgstep5.natDegree ≤ 9 := by unfold Bgstep5; compute_degree!
  have hQ : Qgstep5.natDegree ≤ 8 := by unfold Qgstep5; compute_degree!
  have hN : Ngstep5.natDegree ≤ 9 := by unfold Ngstep5; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep5 * Bgstep5).natDegree ≤ 18 := by
    calc (Agstep5 * Bgstep5).natDegree ≤ Agstep5.natDegree + Bgstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep5).natDegree ≤ S2550F10.natDegree + Qgstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep5 + Ngstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep5 + Ngstep5).natDegree
        ≤ max (S2550F10 * Qgstep5).natDegree Ngstep5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep5, Bgstep5, Qgstep5, Ngstep5, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep6 : (ZMod 1249)[X] := C 495 + C 151 * X + C 112 * X ^ 2 + C 865 * X ^ 3 + C 1200 * X ^ 4 + C 441 * X ^ 5 + C 733 * X ^ 6 + C 1067 * X ^ 7 + C 449 * X ^ 8 + C 793 * X ^ 9
def Bgstep6 : (ZMod 1249)[X] := C 495 + C 151 * X + C 112 * X ^ 2 + C 865 * X ^ 3 + C 1200 * X ^ 4 + C 441 * X ^ 5 + C 733 * X ^ 6 + C 1067 * X ^ 7 + C 449 * X ^ 8 + C 793 * X ^ 9
def Qgstep6 : (ZMod 1249)[X] := C 225 + C 179 * X + C 42 * X ^ 2 + C 396 * X ^ 3 + C 1093 * X ^ 4 + C 546 * X ^ 5 + C 834 * X ^ 6 + C 519 * X ^ 7 + C 602 * X ^ 8
def Ngstep6 : (ZMod 1249)[X] := C 866 + C 826 * X + C 502 * X ^ 2 + C 1063 * X ^ 3 + C 149 * X ^ 4 + C 167 * X ^ 5 + C 323 * X ^ 6 + C 1184 * X ^ 7 + C 996 * X ^ 8 + C 63 * X ^ 9
theorem gstep6 : Agstep6 * Bgstep6 = S2550F10 * Qgstep6 + Ngstep6 := by
  have hA : Agstep6.natDegree ≤ 9 := by unfold Agstep6; compute_degree!
  have hB : Bgstep6.natDegree ≤ 9 := by unfold Bgstep6; compute_degree!
  have hQ : Qgstep6.natDegree ≤ 8 := by unfold Qgstep6; compute_degree!
  have hN : Ngstep6.natDegree ≤ 9 := by unfold Ngstep6; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep6 * Bgstep6).natDegree ≤ 18 := by
    calc (Agstep6 * Bgstep6).natDegree ≤ Agstep6.natDegree + Bgstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep6).natDegree ≤ S2550F10.natDegree + Qgstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep6 + Ngstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep6 + Ngstep6).natDegree
        ≤ max (S2550F10 * Qgstep6).natDegree Ngstep6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep6, Bgstep6, Qgstep6, Ngstep6, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep7 : (ZMod 1249)[X] := C 866 + C 826 * X + C 502 * X ^ 2 + C 1063 * X ^ 3 + C 149 * X ^ 4 + C 167 * X ^ 5 + C 323 * X ^ 6 + C 1184 * X ^ 7 + C 996 * X ^ 8 + C 63 * X ^ 9
def Bgstep7 : (ZMod 1249)[X] := C 866 + C 826 * X + C 502 * X ^ 2 + C 1063 * X ^ 3 + C 149 * X ^ 4 + C 167 * X ^ 5 + C 323 * X ^ 6 + C 1184 * X ^ 7 + C 996 * X ^ 8 + C 63 * X ^ 9
def Qgstep7 : (ZMod 1249)[X] := C 410 + C 168 * X + C 652 * X ^ 2 + C 359 * X ^ 3 + C 630 * X ^ 4 + C 1095 * X ^ 5 + C 1150 * X ^ 6 + C 205 * X ^ 7 + C 222 * X ^ 8
def Ngstep7 : (ZMod 1249)[X] := C 66 + C 1144 * X + C 541 * X ^ 2 + C 701 * X ^ 3 + C 901 * X ^ 4 + C 1071 * X ^ 5 + C 321 * X ^ 6 + C 128 * X ^ 7 + C 1221 * X ^ 8 + C 131 * X ^ 9
theorem gstep7 : Agstep7 * Bgstep7 = S2550F10 * Qgstep7 + Ngstep7 := by
  have hA : Agstep7.natDegree ≤ 9 := by unfold Agstep7; compute_degree!
  have hB : Bgstep7.natDegree ≤ 9 := by unfold Bgstep7; compute_degree!
  have hQ : Qgstep7.natDegree ≤ 8 := by unfold Qgstep7; compute_degree!
  have hN : Ngstep7.natDegree ≤ 9 := by unfold Ngstep7; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep7 * Bgstep7).natDegree ≤ 18 := by
    calc (Agstep7 * Bgstep7).natDegree ≤ Agstep7.natDegree + Bgstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep7).natDegree ≤ S2550F10.natDegree + Qgstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep7 + Ngstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep7 + Ngstep7).natDegree
        ≤ max (S2550F10 * Qgstep7).natDegree Ngstep7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep7, Bgstep7, Qgstep7, Ngstep7, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep8 : (ZMod 1249)[X] := C 66 + C 1144 * X + C 541 * X ^ 2 + C 701 * X ^ 3 + C 901 * X ^ 4 + C 1071 * X ^ 5 + C 321 * X ^ 6 + C 128 * X ^ 7 + C 1221 * X ^ 8 + C 131 * X ^ 9
def Bgstep8 : (ZMod 1249)[X] := C 66 + C 1144 * X + C 541 * X ^ 2 + C 701 * X ^ 3 + C 901 * X ^ 4 + C 1071 * X ^ 5 + C 321 * X ^ 6 + C 128 * X ^ 7 + C 1221 * X ^ 8 + C 131 * X ^ 9
def Qgstep8 : (ZMod 1249)[X] := C 19 + C 600 * X + C 38 * X ^ 2 + C 4 * X ^ 3 + C 479 * X ^ 4 + C 815 * X ^ 5 + C 411 * X ^ 6 + C 556 * X ^ 7 + C 924 * X ^ 8
def Ngstep8 : (ZMod 1249)[X] := C 830 + C 943 * X + C 219 * X ^ 2 + C 354 * X ^ 3 + C 89 * X ^ 4 + C 758 * X ^ 5 + C 900 * X ^ 6 + C 1166 * X ^ 7 + C 1063 * X ^ 8 + C 694 * X ^ 9
theorem gstep8 : Agstep8 * Bgstep8 = S2550F10 * Qgstep8 + Ngstep8 := by
  have hA : Agstep8.natDegree ≤ 9 := by unfold Agstep8; compute_degree!
  have hB : Bgstep8.natDegree ≤ 9 := by unfold Bgstep8; compute_degree!
  have hQ : Qgstep8.natDegree ≤ 8 := by unfold Qgstep8; compute_degree!
  have hN : Ngstep8.natDegree ≤ 9 := by unfold Ngstep8; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep8 * Bgstep8).natDegree ≤ 18 := by
    calc (Agstep8 * Bgstep8).natDegree ≤ Agstep8.natDegree + Bgstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep8).natDegree ≤ S2550F10.natDegree + Qgstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep8 + Ngstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep8 + Ngstep8).natDegree
        ≤ max (S2550F10 * Qgstep8).natDegree Ngstep8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep8, Bgstep8, Qgstep8, Ngstep8, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep9 : (ZMod 1249)[X] := C 830 + C 943 * X + C 219 * X ^ 2 + C 354 * X ^ 3 + C 89 * X ^ 4 + C 758 * X ^ 5 + C 900 * X ^ 6 + C 1166 * X ^ 7 + C 1063 * X ^ 8 + C 694 * X ^ 9
def Bgstep9 : (ZMod 1249)[X] := C 830 + C 943 * X + C 219 * X ^ 2 + C 354 * X ^ 3 + C 89 * X ^ 4 + C 758 * X ^ 5 + C 900 * X ^ 6 + C 1166 * X ^ 7 + C 1063 * X ^ 8 + C 694 * X ^ 9
def Qgstep9 : (ZMod 1249)[X] := C 1129 + C 73 * X + C 93 * X ^ 2 + C 1007 * X ^ 3 + C 161 * X ^ 4 + C 406 * X ^ 5 + C 953 * X ^ 6 + C 553 * X ^ 7 + C 771 * X ^ 8
def Ngstep9 : (ZMod 1249)[X] := C 357 + C 445 * X + C 737 * X ^ 2 + C 242 * X ^ 3 + C 1004 * X ^ 4 + C 1090 * X ^ 5 + C 679 * X ^ 6 + C 975 * X ^ 7 + C 711 * X ^ 8 + C 1014 * X ^ 9
theorem gstep9 : Agstep9 * Bgstep9 = S2550F10 * Qgstep9 + Ngstep9 := by
  have hA : Agstep9.natDegree ≤ 9 := by unfold Agstep9; compute_degree!
  have hB : Bgstep9.natDegree ≤ 9 := by unfold Bgstep9; compute_degree!
  have hQ : Qgstep9.natDegree ≤ 8 := by unfold Qgstep9; compute_degree!
  have hN : Ngstep9.natDegree ≤ 9 := by unfold Ngstep9; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep9 * Bgstep9).natDegree ≤ 18 := by
    calc (Agstep9 * Bgstep9).natDegree ≤ Agstep9.natDegree + Bgstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep9).natDegree ≤ S2550F10.natDegree + Qgstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep9 + Ngstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep9 + Ngstep9).natDegree
        ≤ max (S2550F10 * Qgstep9).natDegree Ngstep9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep9, Bgstep9, Qgstep9, Ngstep9, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep10 : (ZMod 1249)[X] := C 357 + C 445 * X + C 737 * X ^ 2 + C 242 * X ^ 3 + C 1004 * X ^ 4 + C 1090 * X ^ 5 + C 679 * X ^ 6 + C 975 * X ^ 7 + C 711 * X ^ 8 + C 1014 * X ^ 9
def Bgstep10 : (ZMod 1249)[X] := C 357 + C 445 * X + C 737 * X ^ 2 + C 242 * X ^ 3 + C 1004 * X ^ 4 + C 1090 * X ^ 5 + C 679 * X ^ 6 + C 975 * X ^ 7 + C 711 * X ^ 8 + C 1014 * X ^ 9
def Qgstep10 : (ZMod 1249)[X] := C 370 + C 480 * X + C 361 * X ^ 2 + C 519 * X ^ 3 + C 1229 * X ^ 4 + C 1101 * X ^ 5 + C 1087 * X ^ 6 + C 859 * X ^ 7 + C 269 * X ^ 8
def Ngstep10 : (ZMod 1249)[X] := C 279 + C 392 * X + C 482 * X ^ 2 + C 1145 * X ^ 3 + C 783 * X ^ 4 + C 1187 * X ^ 5 + C 1137 * X ^ 6 + C 448 * X ^ 7 + C 891 * X ^ 8 + C 365 * X ^ 9
theorem gstep10 : Agstep10 * Bgstep10 = S2550F10 * Qgstep10 + Ngstep10 := by
  have hA : Agstep10.natDegree ≤ 9 := by unfold Agstep10; compute_degree!
  have hB : Bgstep10.natDegree ≤ 9 := by unfold Bgstep10; compute_degree!
  have hQ : Qgstep10.natDegree ≤ 8 := by unfold Qgstep10; compute_degree!
  have hN : Ngstep10.natDegree ≤ 9 := by unfold Ngstep10; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep10 * Bgstep10).natDegree ≤ 18 := by
    calc (Agstep10 * Bgstep10).natDegree ≤ Agstep10.natDegree + Bgstep10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep10).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep10).natDegree ≤ S2550F10.natDegree + Qgstep10.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep10 + Ngstep10).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep10 + Ngstep10).natDegree
        ≤ max (S2550F10 * Qgstep10).natDegree Ngstep10.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep10, Bgstep10, Qgstep10, Ngstep10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep11 : (ZMod 1249)[X] := C 279 + C 392 * X + C 482 * X ^ 2 + C 1145 * X ^ 3 + C 783 * X ^ 4 + C 1187 * X ^ 5 + C 1137 * X ^ 6 + C 448 * X ^ 7 + C 891 * X ^ 8 + C 365 * X ^ 9
def Bgstep11 : (ZMod 1249)[X] := C 279 + C 392 * X + C 482 * X ^ 2 + C 1145 * X ^ 3 + C 783 * X ^ 4 + C 1187 * X ^ 5 + C 1137 * X ^ 6 + C 448 * X ^ 7 + C 891 * X ^ 8 + C 365 * X ^ 9
def Qgstep11 : (ZMod 1249)[X] := C 204 + C 553 * X + C 1082 * X ^ 2 + C 665 * X ^ 3 + C 1089 * X ^ 4 + C 542 * X ^ 5 + C 980 * X ^ 6 + C 651 * X ^ 7 + C 831 * X ^ 8
def Ngstep11 : (ZMod 1249)[X] := C 738 + C 273 * X + C 578 * X ^ 2 + C 928 * X ^ 3 + C 1090 * X ^ 4 + C 663 * X ^ 5 + C 483 * X ^ 6 + C 1181 * X ^ 7 + C 503 * X ^ 8 + C 166 * X ^ 9
theorem gstep11 : Agstep11 * Bgstep11 = S2550F10 * Qgstep11 + Ngstep11 := by
  have hA : Agstep11.natDegree ≤ 9 := by unfold Agstep11; compute_degree!
  have hB : Bgstep11.natDegree ≤ 9 := by unfold Bgstep11; compute_degree!
  have hQ : Qgstep11.natDegree ≤ 8 := by unfold Qgstep11; compute_degree!
  have hN : Ngstep11.natDegree ≤ 9 := by unfold Ngstep11; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep11 * Bgstep11).natDegree ≤ 18 := by
    calc (Agstep11 * Bgstep11).natDegree ≤ Agstep11.natDegree + Bgstep11.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep11).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep11).natDegree ≤ S2550F10.natDegree + Qgstep11.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep11 + Ngstep11).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep11 + Ngstep11).natDegree
        ≤ max (S2550F10 * Qgstep11).natDegree Ngstep11.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep11, Bgstep11, Qgstep11, Ngstep11, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep12 : (ZMod 1249)[X] := C 738 + C 273 * X + C 578 * X ^ 2 + C 928 * X ^ 3 + C 1090 * X ^ 4 + C 663 * X ^ 5 + C 483 * X ^ 6 + C 1181 * X ^ 7 + C 503 * X ^ 8 + C 166 * X ^ 9
def Bgstep12 : (ZMod 1249)[X] := C 738 + C 273 * X + C 578 * X ^ 2 + C 928 * X ^ 3 + C 1090 * X ^ 4 + C 663 * X ^ 5 + C 483 * X ^ 6 + C 1181 * X ^ 7 + C 503 * X ^ 8 + C 166 * X ^ 9
def Qgstep12 : (ZMod 1249)[X] := C 1045 + C 677 * X + C 721 * X ^ 2 + C 1119 * X ^ 3 + C 114 * X ^ 4 + C 599 * X ^ 5 + C 399 * X ^ 6 + C 134 * X ^ 7 + C 78 * X ^ 8
def Ngstep12 : (ZMod 1249)[X] := C 994 + C 437 * X + C 1108 * X ^ 2 + C 59 * X ^ 3 + C 373 * X ^ 4 + C 392 * X ^ 5 + C 805 * X ^ 6 + C 204 * X ^ 7 + C 599 * X ^ 8 + C 240 * X ^ 9
theorem gstep12 : Agstep12 * Bgstep12 = S2550F10 * Qgstep12 + Ngstep12 := by
  have hA : Agstep12.natDegree ≤ 9 := by unfold Agstep12; compute_degree!
  have hB : Bgstep12.natDegree ≤ 9 := by unfold Bgstep12; compute_degree!
  have hQ : Qgstep12.natDegree ≤ 8 := by unfold Qgstep12; compute_degree!
  have hN : Ngstep12.natDegree ≤ 9 := by unfold Ngstep12; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep12 * Bgstep12).natDegree ≤ 18 := by
    calc (Agstep12 * Bgstep12).natDegree ≤ Agstep12.natDegree + Bgstep12.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep12).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep12).natDegree ≤ S2550F10.natDegree + Qgstep12.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep12 + Ngstep12).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep12 + Ngstep12).natDegree
        ≤ max (S2550F10 * Qgstep12).natDegree Ngstep12.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep12, Bgstep12, Qgstep12, Ngstep12, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep13 : (ZMod 1249)[X] := C 994 + C 437 * X + C 1108 * X ^ 2 + C 59 * X ^ 3 + C 373 * X ^ 4 + C 392 * X ^ 5 + C 805 * X ^ 6 + C 204 * X ^ 7 + C 599 * X ^ 8 + C 240 * X ^ 9
def Bgstep13 : (ZMod 1249)[X] := C 994 + C 437 * X + C 1108 * X ^ 2 + C 59 * X ^ 3 + C 373 * X ^ 4 + C 392 * X ^ 5 + C 805 * X ^ 6 + C 204 * X ^ 7 + C 599 * X ^ 8 + C 240 * X ^ 9
def Qgstep13 : (ZMod 1249)[X] := C 685 + C 320 * X + C 354 * X ^ 2 + C 1115 * X ^ 3 + C 666 * X ^ 4 + C 663 * X ^ 5 + C 973 * X ^ 6 + C 713 * X ^ 7 + C 146 * X ^ 8
def Ngstep13 : (ZMod 1249)[X] := C 1208 + C 1151 * X + C 1057 * X ^ 2 + C 645 * X ^ 3 + C 407 * X ^ 4 + C 114 * X ^ 5 + C 918 * X ^ 6 + C 746 * X ^ 7 + C 998 * X ^ 8 + C 1067 * X ^ 9
theorem gstep13 : Agstep13 * Bgstep13 = S2550F10 * Qgstep13 + Ngstep13 := by
  have hA : Agstep13.natDegree ≤ 9 := by unfold Agstep13; compute_degree!
  have hB : Bgstep13.natDegree ≤ 9 := by unfold Bgstep13; compute_degree!
  have hQ : Qgstep13.natDegree ≤ 8 := by unfold Qgstep13; compute_degree!
  have hN : Ngstep13.natDegree ≤ 9 := by unfold Ngstep13; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep13 * Bgstep13).natDegree ≤ 18 := by
    calc (Agstep13 * Bgstep13).natDegree ≤ Agstep13.natDegree + Bgstep13.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep13).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep13).natDegree ≤ S2550F10.natDegree + Qgstep13.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep13 + Ngstep13).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep13 + Ngstep13).natDegree
        ≤ max (S2550F10 * Qgstep13).natDegree Ngstep13.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep13, Bgstep13, Qgstep13, Ngstep13, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep14 : (ZMod 1249)[X] := C 1208 + C 1151 * X + C 1057 * X ^ 2 + C 645 * X ^ 3 + C 407 * X ^ 4 + C 114 * X ^ 5 + C 918 * X ^ 6 + C 746 * X ^ 7 + C 998 * X ^ 8 + C 1067 * X ^ 9
def Bgstep14 : (ZMod 1249)[X] := C 1208 + C 1151 * X + C 1057 * X ^ 2 + C 645 * X ^ 3 + C 407 * X ^ 4 + C 114 * X ^ 5 + C 918 * X ^ 6 + C 746 * X ^ 7 + C 998 * X ^ 8 + C 1067 * X ^ 9
def Qgstep14 : (ZMod 1249)[X] := C 724 + C 1015 * X + C 236 * X ^ 2 + C 224 * X ^ 3 + C 1142 * X ^ 4 + C 969 * X ^ 5 + C 972 * X ^ 6 + C 640 * X ^ 7 + C 650 * X ^ 8
def Ngstep14 : (ZMod 1249)[X] := C 176 + C 1090 * X + C 313 * X ^ 2 + C 922 * X ^ 3 + C 830 * X ^ 4 + C 174 * X ^ 5 + C 85 * X ^ 6 + C 733 * X ^ 7 + C 997 * X ^ 8 + C 781 * X ^ 9
theorem gstep14 : Agstep14 * Bgstep14 = S2550F10 * Qgstep14 + Ngstep14 := by
  have hA : Agstep14.natDegree ≤ 9 := by unfold Agstep14; compute_degree!
  have hB : Bgstep14.natDegree ≤ 9 := by unfold Bgstep14; compute_degree!
  have hQ : Qgstep14.natDegree ≤ 8 := by unfold Qgstep14; compute_degree!
  have hN : Ngstep14.natDegree ≤ 9 := by unfold Ngstep14; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep14 * Bgstep14).natDegree ≤ 18 := by
    calc (Agstep14 * Bgstep14).natDegree ≤ Agstep14.natDegree + Bgstep14.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep14).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep14).natDegree ≤ S2550F10.natDegree + Qgstep14.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep14 + Ngstep14).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep14 + Ngstep14).natDegree
        ≤ max (S2550F10 * Qgstep14).natDegree Ngstep14.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep14, Bgstep14, Qgstep14, Ngstep14, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep15 : (ZMod 1249)[X] := C 176 + C 1090 * X + C 313 * X ^ 2 + C 922 * X ^ 3 + C 830 * X ^ 4 + C 174 * X ^ 5 + C 85 * X ^ 6 + C 733 * X ^ 7 + C 997 * X ^ 8 + C 781 * X ^ 9
def Bgstep15 : (ZMod 1249)[X] := C 176 + C 1090 * X + C 313 * X ^ 2 + C 922 * X ^ 3 + C 830 * X ^ 4 + C 174 * X ^ 5 + C 85 * X ^ 6 + C 733 * X ^ 7 + C 997 * X ^ 8 + C 781 * X ^ 9
def Qgstep15 : (ZMod 1249)[X] := C 872 + C 570 * X + C 268 * X ^ 2 + C 1082 * X ^ 3 + C 696 * X ^ 4 + C 268 * X ^ 5 + C 754 * X ^ 6 + C 1175 * X ^ 7 + C 449 * X ^ 8
def Ngstep15 : (ZMod 1249)[X] := C 1085 + C 754 * X + C 95 * X ^ 2 + C 390 * X ^ 3 + C 888 * X ^ 4 + C 1009 * X ^ 5 + C 513 * X ^ 6 + C 642 * X ^ 7 + C 266 * X ^ 8 + C 447 * X ^ 9
theorem gstep15 : Agstep15 * Bgstep15 = S2550F10 * Qgstep15 + Ngstep15 := by
  have hA : Agstep15.natDegree ≤ 9 := by unfold Agstep15; compute_degree!
  have hB : Bgstep15.natDegree ≤ 9 := by unfold Bgstep15; compute_degree!
  have hQ : Qgstep15.natDegree ≤ 8 := by unfold Qgstep15; compute_degree!
  have hN : Ngstep15.natDegree ≤ 9 := by unfold Ngstep15; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep15 * Bgstep15).natDegree ≤ 18 := by
    calc (Agstep15 * Bgstep15).natDegree ≤ Agstep15.natDegree + Bgstep15.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep15).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep15).natDegree ≤ S2550F10.natDegree + Qgstep15.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep15 + Ngstep15).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep15 + Ngstep15).natDegree
        ≤ max (S2550F10 * Qgstep15).natDegree Ngstep15.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep15, Bgstep15, Qgstep15, Ngstep15, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep16 : (ZMod 1249)[X] := C 1085 + C 754 * X + C 95 * X ^ 2 + C 390 * X ^ 3 + C 888 * X ^ 4 + C 1009 * X ^ 5 + C 513 * X ^ 6 + C 642 * X ^ 7 + C 266 * X ^ 8 + C 447 * X ^ 9
def Bgstep16 : (ZMod 1249)[X] := C 1085 + C 754 * X + C 95 * X ^ 2 + C 390 * X ^ 3 + C 888 * X ^ 4 + C 1009 * X ^ 5 + C 513 * X ^ 6 + C 642 * X ^ 7 + C 266 * X ^ 8 + C 447 * X ^ 9
def Qgstep16 : (ZMod 1249)[X] := C 178 + C 1218 * X + C 120 * X ^ 2 + C 50 * X ^ 3 + C 379 * X ^ 4 + C 85 * X ^ 5 + C 48 * X ^ 6 + C 678 * X ^ 7 + C 1218 * X ^ 8
def Ngstep16 : (ZMod 1249)[X] := C 1094 + C 912 * X + C 1121 * X ^ 2 + C 387 * X ^ 3 + C 145 * X ^ 4 + C 1211 * X ^ 5 + C 291 * X ^ 6 + C 672 * X ^ 7 + C 1142 * X ^ 8 + C 978 * X ^ 9
theorem gstep16 : Agstep16 * Bgstep16 = S2550F10 * Qgstep16 + Ngstep16 := by
  have hA : Agstep16.natDegree ≤ 9 := by unfold Agstep16; compute_degree!
  have hB : Bgstep16.natDegree ≤ 9 := by unfold Bgstep16; compute_degree!
  have hQ : Qgstep16.natDegree ≤ 8 := by unfold Qgstep16; compute_degree!
  have hN : Ngstep16.natDegree ≤ 9 := by unfold Ngstep16; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep16 * Bgstep16).natDegree ≤ 18 := by
    calc (Agstep16 * Bgstep16).natDegree ≤ Agstep16.natDegree + Bgstep16.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep16).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep16).natDegree ≤ S2550F10.natDegree + Qgstep16.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep16 + Ngstep16).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep16 + Ngstep16).natDegree
        ≤ max (S2550F10 * Qgstep16).natDegree Ngstep16.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep16, Bgstep16, Qgstep16, Ngstep16, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Agstep17 : (ZMod 1249)[X] := C 1094 + C 912 * X + C 1121 * X ^ 2 + C 387 * X ^ 3 + C 145 * X ^ 4 + C 1211 * X ^ 5 + C 291 * X ^ 6 + C 672 * X ^ 7 + C 1142 * X ^ 8 + C 978 * X ^ 9
def Bgstep17 : (ZMod 1249)[X] := C 1094 + C 912 * X + C 1121 * X ^ 2 + C 387 * X ^ 3 + C 145 * X ^ 4 + C 1211 * X ^ 5 + C 291 * X ^ 6 + C 672 * X ^ 7 + C 1142 * X ^ 8 + C 978 * X ^ 9
def Qgstep17 : (ZMod 1249)[X] := C 554 + C 807 * X + C 277 * X ^ 2 + C 720 * X ^ 3 + C 16 * X ^ 4 + C 156 * X ^ 5 + C 777 * X ^ 6 + C 654 * X ^ 7 + C 999 * X ^ 8
def Ngstep17 : (ZMod 1249)[X] := C 1216 + C 331 * X + C 278 * X ^ 2 + C 582 * X ^ 3 + C 778 * X ^ 4 + C 897 * X ^ 5 + C 168 * X ^ 6 + C 698 * X ^ 7 + C 790 * X ^ 8 + C 994 * X ^ 9
theorem gstep17 : Agstep17 * Bgstep17 = S2550F10 * Qgstep17 + Ngstep17 := by
  have hA : Agstep17.natDegree ≤ 9 := by unfold Agstep17; compute_degree!
  have hB : Bgstep17.natDegree ≤ 9 := by unfold Bgstep17; compute_degree!
  have hQ : Qgstep17.natDegree ≤ 8 := by unfold Qgstep17; compute_degree!
  have hN : Ngstep17.natDegree ≤ 9 := by unfold Ngstep17; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Agstep17 * Bgstep17).natDegree ≤ 18 := by
    calc (Agstep17 * Bgstep17).natDegree ≤ Agstep17.natDegree + Bgstep17.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qgstep17).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep17).natDegree ≤ S2550F10.natDegree + Qgstep17.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qgstep17 + Ngstep17).natDegree ≤ 18 := by
    calc (S2550F10 * Qgstep17 + Ngstep17).natDegree
        ≤ max (S2550F10 * Qgstep17).natDegree Ngstep17.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Agstep17, Bgstep17, Qgstep17, Ngstep17, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2565Batch6CorrectActual

end