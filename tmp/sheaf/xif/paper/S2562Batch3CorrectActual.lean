import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual

def V0 : (ZMod 1249)[X] := C 644 + C 889 * X + C 20 * X ^ 2 + C 552 * X ^ 3 + C 1015 * X ^ 4 + C 1199 * X ^ 5 + C 1208 * X ^ 6 + C 524 * X ^ 7 + C 407 * X ^ 8 + C 264 * X ^ 9
def V1 : (ZMod 1249)[X] := C 836 + C 723 * X + C 352 * X ^ 2 + C 587 * X ^ 3 + C 708 * X ^ 4 + C 162 * X ^ 5 + C 71 * X ^ 6 + C 1235 * X ^ 7 + C 651 * X ^ 8 + C 1108 * X ^ 9
def V2 : (ZMod 1249)[X] := C 1234 + C 815 * X + C 357 * X ^ 2 + C 942 * X ^ 3 + C 855 * X ^ 4 + C 726 * X ^ 5 + C 636 * X ^ 6 + C 201 * X ^ 7 + C 656 * X ^ 8 + C 619 * X ^ 9
def V3 : (ZMod 1249)[X] := C 41 + C 1137 * X + C 574 * X ^ 2 + C 191 * X ^ 3 + C 781 * X ^ 4 + C 702 * X ^ 5 + C 347 * X ^ 6 + C 706 * X ^ 7 + C 604 * X ^ 8 + C 135 * X ^ 9
def V4 : (ZMod 1249)[X] := C 871 + C 629 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
def Avstep0 : (ZMod 1249)[X] := C 644 + C 889 * X + C 20 * X ^ 2 + C 552 * X ^ 3 + C 1015 * X ^ 4 + C 1199 * X ^ 5 + C 1208 * X ^ 6 + C 524 * X ^ 7 + C 407 * X ^ 8 + C 264 * X ^ 9
def Bvstep0 : (ZMod 1249)[X] := C 366 + C 858 * X + C 152 * X ^ 2 + C 1007 * X ^ 3 + C 685 * X ^ 4 + C 421 * X ^ 5 + C 74 * X ^ 6 + C 523 * X ^ 7 + C 568 * X ^ 8 + C 954 * X ^ 9
def Qvstep0 : (ZMod 1249)[X] := C 939 + C 294 * X + C 410 * X ^ 2 + C 1065 * X ^ 3 + C 305 * X ^ 4 + C 350 * X ^ 5 + C 1236 * X ^ 6 + C 802 * X ^ 7 + C 807 * X ^ 8
def Nvstep0 : (ZMod 1249)[X] := C 836 + C 723 * X + C 352 * X ^ 2 + C 587 * X ^ 3 + C 708 * X ^ 4 + C 162 * X ^ 5 + C 71 * X ^ 6 + C 1235 * X ^ 7 + C 651 * X ^ 8 + C 1108 * X ^ 9
theorem vstep0 : Avstep0 * Bvstep0 = S2550F10 * Qvstep0 + Nvstep0 := by
  have hA : Avstep0.natDegree ≤ 9 := by unfold Avstep0; compute_degree!
  have hB : Bvstep0.natDegree ≤ 9 := by unfold Bvstep0; compute_degree!
  have hQ : Qvstep0.natDegree ≤ 8 := by unfold Qvstep0; compute_degree!
  have hN : Nvstep0.natDegree ≤ 9 := by unfold Nvstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Avstep0 * Bvstep0).natDegree ≤ 18 := by
    calc (Avstep0 * Bvstep0).natDegree ≤ Avstep0.natDegree + Bvstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qvstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep0).natDegree ≤ S2550F10.natDegree + Qvstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qvstep0 + Nvstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep0 + Nvstep0).natDegree
        ≤ max (S2550F10 * Qvstep0).natDegree Nvstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Avstep0, Bvstep0, Qvstep0, Nvstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Avstep1 : (ZMod 1249)[X] := C 836 + C 723 * X + C 352 * X ^ 2 + C 587 * X ^ 3 + C 708 * X ^ 4 + C 162 * X ^ 5 + C 71 * X ^ 6 + C 1235 * X ^ 7 + C 651 * X ^ 8 + C 1108 * X ^ 9
def Bvstep1 : (ZMod 1249)[X] := C 1173 + C 570 * X + C 176 * X ^ 2 + C 825 * X ^ 3 + C 1243 * X ^ 4 + C 672 * X ^ 5 + C 1150 * X ^ 6 + C 696 * X ^ 7 + C 985 * X ^ 8 + C 419 * X ^ 9
def Qvstep1 : (ZMod 1249)[X] := C 1245 + C 578 * X + C 474 * X ^ 2 + C 362 * X ^ 3 + C 8 * X ^ 4 + C 810 * X ^ 5 + C 1162 * X ^ 6 + C 982 * X ^ 7 + C 873 * X ^ 8
def Nvstep1 : (ZMod 1249)[X] := C 1234 + C 815 * X + C 357 * X ^ 2 + C 942 * X ^ 3 + C 855 * X ^ 4 + C 726 * X ^ 5 + C 636 * X ^ 6 + C 201 * X ^ 7 + C 656 * X ^ 8 + C 619 * X ^ 9
theorem vstep1 : Avstep1 * Bvstep1 = S2550F10 * Qvstep1 + Nvstep1 := by
  have hA : Avstep1.natDegree ≤ 9 := by unfold Avstep1; compute_degree!
  have hB : Bvstep1.natDegree ≤ 9 := by unfold Bvstep1; compute_degree!
  have hQ : Qvstep1.natDegree ≤ 8 := by unfold Qvstep1; compute_degree!
  have hN : Nvstep1.natDegree ≤ 9 := by unfold Nvstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Avstep1 * Bvstep1).natDegree ≤ 18 := by
    calc (Avstep1 * Bvstep1).natDegree ≤ Avstep1.natDegree + Bvstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qvstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep1).natDegree ≤ S2550F10.natDegree + Qvstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qvstep1 + Nvstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep1 + Nvstep1).natDegree
        ≤ max (S2550F10 * Qvstep1).natDegree Nvstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Avstep1, Bvstep1, Qvstep1, Nvstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Avstep2 : (ZMod 1249)[X] := C 1234 + C 815 * X + C 357 * X ^ 2 + C 942 * X ^ 3 + C 855 * X ^ 4 + C 726 * X ^ 5 + C 636 * X ^ 6 + C 201 * X ^ 7 + C 656 * X ^ 8 + C 619 * X ^ 9
def Bvstep2 : (ZMod 1249)[X] := C 1156 + C 41 * X + C 615 * X ^ 2 + C 231 * X ^ 3 + C 400 * X ^ 4 + C 609 * X ^ 5 + C 1080 * X ^ 6 + C 791 * X ^ 7 + C 1220 * X ^ 8 + C 1015 * X ^ 9
def Qvstep2 : (ZMod 1249)[X] := C 980 + C 669 * X + C 998 * X ^ 2 + C 19 * X ^ 3 + C 354 * X ^ 4 + C 185 * X ^ 5 + C 270 * X ^ 6 + C 480 * X ^ 7 + C 38 * X ^ 8
def Nvstep2 : (ZMod 1249)[X] := C 41 + C 1137 * X + C 574 * X ^ 2 + C 191 * X ^ 3 + C 781 * X ^ 4 + C 702 * X ^ 5 + C 347 * X ^ 6 + C 706 * X ^ 7 + C 604 * X ^ 8 + C 135 * X ^ 9
theorem vstep2 : Avstep2 * Bvstep2 = S2550F10 * Qvstep2 + Nvstep2 := by
  have hA : Avstep2.natDegree ≤ 9 := by unfold Avstep2; compute_degree!
  have hB : Bvstep2.natDegree ≤ 9 := by unfold Bvstep2; compute_degree!
  have hQ : Qvstep2.natDegree ≤ 8 := by unfold Qvstep2; compute_degree!
  have hN : Nvstep2.natDegree ≤ 9 := by unfold Nvstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Avstep2 * Bvstep2).natDegree ≤ 18 := by
    calc (Avstep2 * Bvstep2).natDegree ≤ Avstep2.natDegree + Bvstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qvstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep2).natDegree ≤ S2550F10.natDegree + Qvstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qvstep2 + Nvstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep2 + Nvstep2).natDegree
        ≤ max (S2550F10 * Qvstep2).natDegree Nvstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Avstep2, Bvstep2, Qvstep2, Nvstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Avstep3 : (ZMod 1249)[X] := C 41 + C 1137 * X + C 574 * X ^ 2 + C 191 * X ^ 3 + C 781 * X ^ 4 + C 702 * X ^ 5 + C 347 * X ^ 6 + C 706 * X ^ 7 + C 604 * X ^ 8 + C 135 * X ^ 9
def Bvstep3 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
def Qvstep3 : (ZMod 1249)[X] := C 928 + C 927 * X + C 100 * X ^ 2 + C 1075 * X ^ 3 + C 516 * X ^ 4 + C 689 * X ^ 5 + C 833 * X ^ 6 + C 965 * X ^ 7 + C 66 * X ^ 8
def Nvstep3 : (ZMod 1249)[X] := C 871 + C 629 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
theorem vstep3 : Avstep3 * Bvstep3 = S2550F10 * Qvstep3 + Nvstep3 := by
  have hA : Avstep3.natDegree ≤ 9 := by unfold Avstep3; compute_degree!
  have hB : Bvstep3.natDegree ≤ 9 := by unfold Bvstep3; compute_degree!
  have hQ : Qvstep3.natDegree ≤ 8 := by unfold Qvstep3; compute_degree!
  have hN : Nvstep3.natDegree ≤ 9 := by unfold Nvstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Avstep3 * Bvstep3).natDegree ≤ 18 := by
    calc (Avstep3 * Bvstep3).natDegree ≤ Avstep3.natDegree + Bvstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qvstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep3).natDegree ≤ S2550F10.natDegree + Qvstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qvstep3 + Nvstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qvstep3 + Nvstep3).natDegree
        ≤ max (S2550F10 * Qvstep3).natDegree Nvstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Avstep3, Bvstep3, Qvstep3, Nvstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def W0 : (ZMod 1249)[X] := C 871 + C 629 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
def W1 : (ZMod 1249)[X] := C 772 + C 188 * X + C 1208 * X ^ 2 + C 1035 * X ^ 3 + C 218 * X ^ 4 + C 650 * X ^ 5 + C 837 * X ^ 6 + C 285 * X ^ 7 + C 709 * X ^ 8 + C 1130 * X ^ 9
def W2 : (ZMod 1249)[X] := C 114 + C 215 * X + C 1065 * X ^ 2 + C 1006 * X ^ 3 + C 403 * X ^ 4 + C 264 * X ^ 5 + C 603 * X ^ 6 + C 927 * X ^ 7 + C 1062 * X ^ 8 + C 797 * X ^ 9
def W3 : (ZMod 1249)[X] := C 725 + C 641 * X + C 684 * X ^ 2 + C 263 * X ^ 3 + C 920 * X ^ 4 + C 163 * X ^ 5 + C 70 * X ^ 6 + C 810 * X ^ 7 + C 193 * X ^ 8 + C 840 * X ^ 9
def W4 : (ZMod 1249)[X] := C 1139 + C 794 * X + C 1095 * X ^ 2 + C 682 * X ^ 3 + C 28 * X ^ 4 + C 566 * X ^ 5 + C 788 * X ^ 6 + C 715 * X ^ 7 + C 1007 * X ^ 8 + C 187 * X ^ 9
def W5 : (ZMod 1249)[X] := C 133 + C 294 * X + C 958 * X ^ 2 + C 531 * X ^ 3 + C 752 * X ^ 4 + C 967 * X ^ 5 + C 311 * X ^ 6 + C 854 * X ^ 7 + C 236 * X ^ 8 + C 871 * X ^ 9
def W6 : (ZMod 1249)[X] := C 591 + C 798 * X + C 929 * X ^ 2 + C 833 * X ^ 3 + C 891 * X ^ 4 + C 821 * X ^ 5 + C 193 * X ^ 6 + C 516 * X ^ 7 + C 696 * X ^ 8 + C 552 * X ^ 9
def W7 : (ZMod 1249)[X] := C 919 + C 135 * X + C 1060 * X ^ 2 + C 1133 * X ^ 3 + C 461 * X ^ 4 + C 837 * X ^ 5 + C 819 * X ^ 6 + C 85 * X ^ 7 + C 396 * X ^ 8 + C 1123 * X ^ 9
def W8 : (ZMod 1249)[X] := C 204 + C 1154 * X + C 425 * X ^ 2 + C 529 * X ^ 3 + C 850 * X ^ 4 + C 810 * X ^ 5 + C 934 * X ^ 6 + C 1154 * X ^ 7 + C 549 * X ^ 8 + C 137 * X ^ 9
def W9 : (ZMod 1249)[X] := C 1193 + C 614 * X + C 905 * X ^ 2 + C 441 * X ^ 3 + C 427 * X ^ 4 + C 798 * X ^ 5 + C 805 * X ^ 6 + C 801 * X ^ 7 + C 1187 * X ^ 8 + C 627 * X ^ 9
def W10 : (ZMod 1249)[X] := C 292 + C 107 * X + C 397 * X ^ 2 + C 634 * X ^ 3 + C 925 * X ^ 4 + C 322 * X ^ 5 + C 524 * X ^ 6 + C 1173 * X ^ 7 + C 157 * X ^ 8 + C 457 * X ^ 9
def Awstep0 : (ZMod 1249)[X] := C 871 + C 629 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
def Bwstep0 : (ZMod 1249)[X] := C 871 + C 629 * X + C 1077 * X ^ 2 + C 1032 * X ^ 3 + C 142 * X ^ 4 + C 643 * X ^ 5 + C 946 * X ^ 6 + C 1025 * X ^ 7 + C 796 * X ^ 8 + C 1154 * X ^ 9
def Qwstep0 : (ZMod 1249)[X] := C 357 + C 1244 * X + C 894 * X ^ 2 + C 839 * X ^ 3 + C 220 * X ^ 4 + C 973 * X ^ 5 + C 865 * X ^ 6 + C 270 * X ^ 7 + C 282 * X ^ 8
def Nwstep0 : (ZMod 1249)[X] := C 772 + C 188 * X + C 1208 * X ^ 2 + C 1035 * X ^ 3 + C 218 * X ^ 4 + C 650 * X ^ 5 + C 837 * X ^ 6 + C 285 * X ^ 7 + C 709 * X ^ 8 + C 1130 * X ^ 9
theorem wstep0 : Awstep0 * Bwstep0 = S2550F10 * Qwstep0 + Nwstep0 := by
  have hA : Awstep0.natDegree ≤ 9 := by unfold Awstep0; compute_degree!
  have hB : Bwstep0.natDegree ≤ 9 := by unfold Bwstep0; compute_degree!
  have hQ : Qwstep0.natDegree ≤ 8 := by unfold Qwstep0; compute_degree!
  have hN : Nwstep0.natDegree ≤ 9 := by unfold Nwstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep0 * Bwstep0).natDegree ≤ 18 := by
    calc (Awstep0 * Bwstep0).natDegree ≤ Awstep0.natDegree + Bwstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep0).natDegree ≤ S2550F10.natDegree + Qwstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep0 + Nwstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep0 + Nwstep0).natDegree
        ≤ max (S2550F10 * Qwstep0).natDegree Nwstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep0, Bwstep0, Qwstep0, Nwstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep1 : (ZMod 1249)[X] := C 772 + C 188 * X + C 1208 * X ^ 2 + C 1035 * X ^ 3 + C 218 * X ^ 4 + C 650 * X ^ 5 + C 837 * X ^ 6 + C 285 * X ^ 7 + C 709 * X ^ 8 + C 1130 * X ^ 9
def Bwstep1 : (ZMod 1249)[X] := C 772 + C 188 * X + C 1208 * X ^ 2 + C 1035 * X ^ 3 + C 218 * X ^ 4 + C 650 * X ^ 5 + C 837 * X ^ 6 + C 285 * X ^ 7 + C 709 * X ^ 8 + C 1130 * X ^ 9
def Qwstep1 : (ZMod 1249)[X] := C 489 + C 302 * X + C 446 * X ^ 2 + C 905 * X ^ 3 + C 1232 * X ^ 4 + C 563 * X ^ 5 + C 171 * X ^ 6 + C 390 * X ^ 7 + C 422 * X ^ 8
def Nwstep1 : (ZMod 1249)[X] := C 114 + C 215 * X + C 1065 * X ^ 2 + C 1006 * X ^ 3 + C 403 * X ^ 4 + C 264 * X ^ 5 + C 603 * X ^ 6 + C 927 * X ^ 7 + C 1062 * X ^ 8 + C 797 * X ^ 9
theorem wstep1 : Awstep1 * Bwstep1 = S2550F10 * Qwstep1 + Nwstep1 := by
  have hA : Awstep1.natDegree ≤ 9 := by unfold Awstep1; compute_degree!
  have hB : Bwstep1.natDegree ≤ 9 := by unfold Bwstep1; compute_degree!
  have hQ : Qwstep1.natDegree ≤ 8 := by unfold Qwstep1; compute_degree!
  have hN : Nwstep1.natDegree ≤ 9 := by unfold Nwstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep1 * Bwstep1).natDegree ≤ 18 := by
    calc (Awstep1 * Bwstep1).natDegree ≤ Awstep1.natDegree + Bwstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep1).natDegree ≤ S2550F10.natDegree + Qwstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep1 + Nwstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep1 + Nwstep1).natDegree
        ≤ max (S2550F10 * Qwstep1).natDegree Nwstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep1, Bwstep1, Qwstep1, Nwstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep2 : (ZMod 1249)[X] := C 114 + C 215 * X + C 1065 * X ^ 2 + C 1006 * X ^ 3 + C 403 * X ^ 4 + C 264 * X ^ 5 + C 603 * X ^ 6 + C 927 * X ^ 7 + C 1062 * X ^ 8 + C 797 * X ^ 9
def Bwstep2 : (ZMod 1249)[X] := C 114 + C 215 * X + C 1065 * X ^ 2 + C 1006 * X ^ 3 + C 403 * X ^ 4 + C 264 * X ^ 5 + C 603 * X ^ 6 + C 927 * X ^ 7 + C 1062 * X ^ 8 + C 797 * X ^ 9
def Qwstep2 : (ZMod 1249)[X] := C 454 + C 438 * X + C 446 * X ^ 2 + C 430 * X ^ 3 + C 224 * X ^ 4 + C 804 * X ^ 5 + C 364 * X ^ 6 + C 166 * X ^ 7 + C 717 * X ^ 8
def Nwstep2 : (ZMod 1249)[X] := C 725 + C 641 * X + C 684 * X ^ 2 + C 263 * X ^ 3 + C 920 * X ^ 4 + C 163 * X ^ 5 + C 70 * X ^ 6 + C 810 * X ^ 7 + C 193 * X ^ 8 + C 840 * X ^ 9
theorem wstep2 : Awstep2 * Bwstep2 = S2550F10 * Qwstep2 + Nwstep2 := by
  have hA : Awstep2.natDegree ≤ 9 := by unfold Awstep2; compute_degree!
  have hB : Bwstep2.natDegree ≤ 9 := by unfold Bwstep2; compute_degree!
  have hQ : Qwstep2.natDegree ≤ 8 := by unfold Qwstep2; compute_degree!
  have hN : Nwstep2.natDegree ≤ 9 := by unfold Nwstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep2 * Bwstep2).natDegree ≤ 18 := by
    calc (Awstep2 * Bwstep2).natDegree ≤ Awstep2.natDegree + Bwstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep2).natDegree ≤ S2550F10.natDegree + Qwstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep2 + Nwstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep2 + Nwstep2).natDegree
        ≤ max (S2550F10 * Qwstep2).natDegree Nwstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep2, Bwstep2, Qwstep2, Nwstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep3 : (ZMod 1249)[X] := C 725 + C 641 * X + C 684 * X ^ 2 + C 263 * X ^ 3 + C 920 * X ^ 4 + C 163 * X ^ 5 + C 70 * X ^ 6 + C 810 * X ^ 7 + C 193 * X ^ 8 + C 840 * X ^ 9
def Bwstep3 : (ZMod 1249)[X] := C 725 + C 641 * X + C 684 * X ^ 2 + C 263 * X ^ 3 + C 920 * X ^ 4 + C 163 * X ^ 5 + C 70 * X ^ 6 + C 810 * X ^ 7 + C 193 * X ^ 8 + C 840 * X ^ 9
def Qwstep3 : (ZMod 1249)[X] := C 788 + C 876 * X + C 980 * X ^ 2 + C 9 * X ^ 3 + C 808 * X ^ 4 + C 1060 * X ^ 5 + C 286 * X ^ 6 + C 488 * X ^ 7 + C 1164 * X ^ 8
def Nwstep3 : (ZMod 1249)[X] := C 1139 + C 794 * X + C 1095 * X ^ 2 + C 682 * X ^ 3 + C 28 * X ^ 4 + C 566 * X ^ 5 + C 788 * X ^ 6 + C 715 * X ^ 7 + C 1007 * X ^ 8 + C 187 * X ^ 9
theorem wstep3 : Awstep3 * Bwstep3 = S2550F10 * Qwstep3 + Nwstep3 := by
  have hA : Awstep3.natDegree ≤ 9 := by unfold Awstep3; compute_degree!
  have hB : Bwstep3.natDegree ≤ 9 := by unfold Bwstep3; compute_degree!
  have hQ : Qwstep3.natDegree ≤ 8 := by unfold Qwstep3; compute_degree!
  have hN : Nwstep3.natDegree ≤ 9 := by unfold Nwstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep3 * Bwstep3).natDegree ≤ 18 := by
    calc (Awstep3 * Bwstep3).natDegree ≤ Awstep3.natDegree + Bwstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep3).natDegree ≤ S2550F10.natDegree + Qwstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep3 + Nwstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep3 + Nwstep3).natDegree
        ≤ max (S2550F10 * Qwstep3).natDegree Nwstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep3, Bwstep3, Qwstep3, Nwstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep4 : (ZMod 1249)[X] := C 1139 + C 794 * X + C 1095 * X ^ 2 + C 682 * X ^ 3 + C 28 * X ^ 4 + C 566 * X ^ 5 + C 788 * X ^ 6 + C 715 * X ^ 7 + C 1007 * X ^ 8 + C 187 * X ^ 9
def Bwstep4 : (ZMod 1249)[X] := C 1139 + C 794 * X + C 1095 * X ^ 2 + C 682 * X ^ 3 + C 28 * X ^ 4 + C 566 * X ^ 5 + C 788 * X ^ 6 + C 715 * X ^ 7 + C 1007 * X ^ 8 + C 187 * X ^ 9
def Qwstep4 : (ZMod 1249)[X] := C 531 + C 580 * X + C 484 * X ^ 2 + C 389 * X ^ 3 + C 497 * X ^ 4 + C 993 * X ^ 5 + C 322 * X ^ 6 + C 1130 * X ^ 7 + C 1246 * X ^ 8
def Nwstep4 : (ZMod 1249)[X] := C 133 + C 294 * X + C 958 * X ^ 2 + C 531 * X ^ 3 + C 752 * X ^ 4 + C 967 * X ^ 5 + C 311 * X ^ 6 + C 854 * X ^ 7 + C 236 * X ^ 8 + C 871 * X ^ 9
theorem wstep4 : Awstep4 * Bwstep4 = S2550F10 * Qwstep4 + Nwstep4 := by
  have hA : Awstep4.natDegree ≤ 9 := by unfold Awstep4; compute_degree!
  have hB : Bwstep4.natDegree ≤ 9 := by unfold Bwstep4; compute_degree!
  have hQ : Qwstep4.natDegree ≤ 8 := by unfold Qwstep4; compute_degree!
  have hN : Nwstep4.natDegree ≤ 9 := by unfold Nwstep4; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep4 * Bwstep4).natDegree ≤ 18 := by
    calc (Awstep4 * Bwstep4).natDegree ≤ Awstep4.natDegree + Bwstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep4).natDegree ≤ S2550F10.natDegree + Qwstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep4 + Nwstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep4 + Nwstep4).natDegree
        ≤ max (S2550F10 * Qwstep4).natDegree Nwstep4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep4, Bwstep4, Qwstep4, Nwstep4, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep5 : (ZMod 1249)[X] := C 133 + C 294 * X + C 958 * X ^ 2 + C 531 * X ^ 3 + C 752 * X ^ 4 + C 967 * X ^ 5 + C 311 * X ^ 6 + C 854 * X ^ 7 + C 236 * X ^ 8 + C 871 * X ^ 9
def Bwstep5 : (ZMod 1249)[X] := C 133 + C 294 * X + C 958 * X ^ 2 + C 531 * X ^ 3 + C 752 * X ^ 4 + C 967 * X ^ 5 + C 311 * X ^ 6 + C 854 * X ^ 7 + C 236 * X ^ 8 + C 871 * X ^ 9
def Qwstep5 : (ZMod 1249)[X] := C 542 + C 956 * X + C 225 * X ^ 2 + C 555 * X ^ 3 + C 672 * X ^ 4 + C 930 * X ^ 5 + C 694 * X ^ 6 + C 1103 * X ^ 7 + C 498 * X ^ 8
def Nwstep5 : (ZMod 1249)[X] := C 591 + C 798 * X + C 929 * X ^ 2 + C 833 * X ^ 3 + C 891 * X ^ 4 + C 821 * X ^ 5 + C 193 * X ^ 6 + C 516 * X ^ 7 + C 696 * X ^ 8 + C 552 * X ^ 9
theorem wstep5 : Awstep5 * Bwstep5 = S2550F10 * Qwstep5 + Nwstep5 := by
  have hA : Awstep5.natDegree ≤ 9 := by unfold Awstep5; compute_degree!
  have hB : Bwstep5.natDegree ≤ 9 := by unfold Bwstep5; compute_degree!
  have hQ : Qwstep5.natDegree ≤ 8 := by unfold Qwstep5; compute_degree!
  have hN : Nwstep5.natDegree ≤ 9 := by unfold Nwstep5; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep5 * Bwstep5).natDegree ≤ 18 := by
    calc (Awstep5 * Bwstep5).natDegree ≤ Awstep5.natDegree + Bwstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep5).natDegree ≤ S2550F10.natDegree + Qwstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep5 + Nwstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep5 + Nwstep5).natDegree
        ≤ max (S2550F10 * Qwstep5).natDegree Nwstep5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep5, Bwstep5, Qwstep5, Nwstep5, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep6 : (ZMod 1249)[X] := C 591 + C 798 * X + C 929 * X ^ 2 + C 833 * X ^ 3 + C 891 * X ^ 4 + C 821 * X ^ 5 + C 193 * X ^ 6 + C 516 * X ^ 7 + C 696 * X ^ 8 + C 552 * X ^ 9
def Bwstep6 : (ZMod 1249)[X] := C 591 + C 798 * X + C 929 * X ^ 2 + C 833 * X ^ 3 + C 891 * X ^ 4 + C 821 * X ^ 5 + C 193 * X ^ 6 + C 516 * X ^ 7 + C 696 * X ^ 8 + C 552 * X ^ 9
def Qwstep6 : (ZMod 1249)[X] := C 648 + C 801 * X + C 157 * X ^ 2 + C 29 * X ^ 3 + C 474 * X ^ 4 + C 1043 * X ^ 5 + C 821 * X ^ 6 + C 1162 * X ^ 7 + C 1197 * X ^ 8
def Nwstep6 : (ZMod 1249)[X] := C 919 + C 135 * X + C 1060 * X ^ 2 + C 1133 * X ^ 3 + C 461 * X ^ 4 + C 837 * X ^ 5 + C 819 * X ^ 6 + C 85 * X ^ 7 + C 396 * X ^ 8 + C 1123 * X ^ 9
theorem wstep6 : Awstep6 * Bwstep6 = S2550F10 * Qwstep6 + Nwstep6 := by
  have hA : Awstep6.natDegree ≤ 9 := by unfold Awstep6; compute_degree!
  have hB : Bwstep6.natDegree ≤ 9 := by unfold Bwstep6; compute_degree!
  have hQ : Qwstep6.natDegree ≤ 8 := by unfold Qwstep6; compute_degree!
  have hN : Nwstep6.natDegree ≤ 9 := by unfold Nwstep6; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep6 * Bwstep6).natDegree ≤ 18 := by
    calc (Awstep6 * Bwstep6).natDegree ≤ Awstep6.natDegree + Bwstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep6).natDegree ≤ S2550F10.natDegree + Qwstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep6 + Nwstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep6 + Nwstep6).natDegree
        ≤ max (S2550F10 * Qwstep6).natDegree Nwstep6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep6, Bwstep6, Qwstep6, Nwstep6, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep7 : (ZMod 1249)[X] := C 919 + C 135 * X + C 1060 * X ^ 2 + C 1133 * X ^ 3 + C 461 * X ^ 4 + C 837 * X ^ 5 + C 819 * X ^ 6 + C 85 * X ^ 7 + C 396 * X ^ 8 + C 1123 * X ^ 9
def Bwstep7 : (ZMod 1249)[X] := C 919 + C 135 * X + C 1060 * X ^ 2 + C 1133 * X ^ 3 + C 461 * X ^ 4 + C 837 * X ^ 5 + C 819 * X ^ 6 + C 85 * X ^ 7 + C 396 * X ^ 8 + C 1123 * X ^ 9
def Qwstep7 : (ZMod 1249)[X] := C 308 + C 1044 * X + C 337 * X ^ 2 + C 95 * X ^ 3 + C 936 * X ^ 4 + C 700 * X ^ 5 + C 1102 * X ^ 6 + C 1062 * X ^ 7 + C 888 * X ^ 8
def Nwstep7 : (ZMod 1249)[X] := C 204 + C 1154 * X + C 425 * X ^ 2 + C 529 * X ^ 3 + C 850 * X ^ 4 + C 810 * X ^ 5 + C 934 * X ^ 6 + C 1154 * X ^ 7 + C 549 * X ^ 8 + C 137 * X ^ 9
theorem wstep7 : Awstep7 * Bwstep7 = S2550F10 * Qwstep7 + Nwstep7 := by
  have hA : Awstep7.natDegree ≤ 9 := by unfold Awstep7; compute_degree!
  have hB : Bwstep7.natDegree ≤ 9 := by unfold Bwstep7; compute_degree!
  have hQ : Qwstep7.natDegree ≤ 8 := by unfold Qwstep7; compute_degree!
  have hN : Nwstep7.natDegree ≤ 9 := by unfold Nwstep7; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep7 * Bwstep7).natDegree ≤ 18 := by
    calc (Awstep7 * Bwstep7).natDegree ≤ Awstep7.natDegree + Bwstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep7).natDegree ≤ S2550F10.natDegree + Qwstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep7 + Nwstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep7 + Nwstep7).natDegree
        ≤ max (S2550F10 * Qwstep7).natDegree Nwstep7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep7, Bwstep7, Qwstep7, Nwstep7, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep8 : (ZMod 1249)[X] := C 204 + C 1154 * X + C 425 * X ^ 2 + C 529 * X ^ 3 + C 850 * X ^ 4 + C 810 * X ^ 5 + C 934 * X ^ 6 + C 1154 * X ^ 7 + C 549 * X ^ 8 + C 137 * X ^ 9
def Bwstep8 : (ZMod 1249)[X] := C 204 + C 1154 * X + C 425 * X ^ 2 + C 529 * X ^ 3 + C 850 * X ^ 4 + C 810 * X ^ 5 + C 934 * X ^ 6 + C 1154 * X ^ 7 + C 549 * X ^ 8 + C 137 * X ^ 9
def Qwstep8 : (ZMod 1249)[X] := C 916 + C 639 * X + C 55 * X ^ 2 + C 77 * X ^ 3 + C 555 * X ^ 4 + C 1020 * X ^ 5 + C 516 * X ^ 6 + C 1150 * X ^ 7 + C 34 * X ^ 8
def Nwstep8 : (ZMod 1249)[X] := C 1193 + C 614 * X + C 905 * X ^ 2 + C 441 * X ^ 3 + C 427 * X ^ 4 + C 798 * X ^ 5 + C 805 * X ^ 6 + C 801 * X ^ 7 + C 1187 * X ^ 8 + C 627 * X ^ 9
theorem wstep8 : Awstep8 * Bwstep8 = S2550F10 * Qwstep8 + Nwstep8 := by
  have hA : Awstep8.natDegree ≤ 9 := by unfold Awstep8; compute_degree!
  have hB : Bwstep8.natDegree ≤ 9 := by unfold Bwstep8; compute_degree!
  have hQ : Qwstep8.natDegree ≤ 8 := by unfold Qwstep8; compute_degree!
  have hN : Nwstep8.natDegree ≤ 9 := by unfold Nwstep8; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep8 * Bwstep8).natDegree ≤ 18 := by
    calc (Awstep8 * Bwstep8).natDegree ≤ Awstep8.natDegree + Bwstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep8).natDegree ≤ S2550F10.natDegree + Qwstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep8 + Nwstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep8 + Nwstep8).natDegree
        ≤ max (S2550F10 * Qwstep8).natDegree Nwstep8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep8, Bwstep8, Qwstep8, Nwstep8, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Awstep9 : (ZMod 1249)[X] := C 1193 + C 614 * X + C 905 * X ^ 2 + C 441 * X ^ 3 + C 427 * X ^ 4 + C 798 * X ^ 5 + C 805 * X ^ 6 + C 801 * X ^ 7 + C 1187 * X ^ 8 + C 627 * X ^ 9
def Bwstep9 : (ZMod 1249)[X] := C 1193 + C 614 * X + C 905 * X ^ 2 + C 441 * X ^ 3 + C 427 * X ^ 4 + C 798 * X ^ 5 + C 805 * X ^ 6 + C 801 * X ^ 7 + C 1187 * X ^ 8 + C 627 * X ^ 9
def Qwstep9 : (ZMod 1249)[X] := C 315 + C 1137 * X + C 152 * X ^ 2 + C 66 * X ^ 3 + C 285 * X ^ 4 + C 714 * X ^ 5 + C 899 * X ^ 6 + C 499 * X ^ 7 + C 943 * X ^ 8
def Nwstep9 : (ZMod 1249)[X] := C 292 + C 107 * X + C 397 * X ^ 2 + C 634 * X ^ 3 + C 925 * X ^ 4 + C 322 * X ^ 5 + C 524 * X ^ 6 + C 1173 * X ^ 7 + C 157 * X ^ 8 + C 457 * X ^ 9
theorem wstep9 : Awstep9 * Bwstep9 = S2550F10 * Qwstep9 + Nwstep9 := by
  have hA : Awstep9.natDegree ≤ 9 := by unfold Awstep9; compute_degree!
  have hB : Bwstep9.natDegree ≤ 9 := by unfold Bwstep9; compute_degree!
  have hQ : Qwstep9.natDegree ≤ 8 := by unfold Qwstep9; compute_degree!
  have hN : Nwstep9.natDegree ≤ 9 := by unfold Nwstep9; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Awstep9 * Bwstep9).natDegree ≤ 18 := by
    calc (Awstep9 * Bwstep9).natDegree ≤ Awstep9.natDegree + Bwstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qwstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep9).natDegree ≤ S2550F10.natDegree + Qwstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qwstep9 + Nwstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qwstep9 + Nwstep9).natDegree
        ≤ max (S2550F10 * Qwstep9).natDegree Nwstep9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Awstep9, Bwstep9, Qwstep9, Nwstep9, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual

end