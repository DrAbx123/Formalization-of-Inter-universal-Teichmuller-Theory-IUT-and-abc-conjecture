import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual

def T0 : (ZMod 1249)[X] := C 91 + C 1214 * X + C 319 * X ^ 2 + C 805 * X ^ 3 + C 483 * X ^ 4 + C 435 * X ^ 5 + C 1242 * X ^ 6 + C 371 * X ^ 7 + C 124 * X ^ 8 + C 193 * X ^ 9
def T1 : (ZMod 1249)[X] := C 428 + C 197 * X + C 164 * X ^ 2 + C 226 * X ^ 3 + C 199 * X ^ 4 + C 1137 * X ^ 5 + C 1163 * X ^ 6 + C 780 * X ^ 7 + C 1163 * X ^ 8 + C 617 * X ^ 9
def T2 : (ZMod 1249)[X] := C 656 + C 538 * X + C 1242 * X ^ 2 + C 988 * X ^ 3 + C 45 * X ^ 4 + C 358 * X ^ 5 + C 395 * X ^ 6 + C 241 * X ^ 7 + C 245 * X ^ 8 + C 280 * X ^ 9
def T3 : (ZMod 1249)[X] := C 638 + C 237 * X + C 462 * X ^ 2 + C 445 * X ^ 3 + C 530 * X ^ 4 + C 386 * X ^ 5 + C 1217 * X ^ 6 + C 766 * X ^ 7 + C 682 * X ^ 8 + C 825 * X ^ 9
def T4 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
def Atstep0 : (ZMod 1249)[X] := C 91 + C 1214 * X + C 319 * X ^ 2 + C 805 * X ^ 3 + C 483 * X ^ 4 + C 435 * X ^ 5 + C 1242 * X ^ 6 + C 371 * X ^ 7 + C 124 * X ^ 8 + C 193 * X ^ 9
def Btstep0 : (ZMod 1249)[X] := C 933 + C 976 * X + C 1083 * X ^ 2 + C 1020 * X ^ 3 + C 954 * X ^ 4 + C 30 * X ^ 5 + C 223 * X ^ 6 + C 46 * X ^ 7 + C 498 * X ^ 8 + C 892 * X ^ 9
def Qtstep0 : (ZMod 1249)[X] := C 1147 + C 74 * X + C 32 * X ^ 2 + C 817 * X ^ 3 + C 400 * X ^ 4 + C 1065 * X ^ 5 + C 203 * X ^ 6 + C 651 * X ^ 7 + C 1043 * X ^ 8
def Ntstep0 : (ZMod 1249)[X] := C 428 + C 197 * X + C 164 * X ^ 2 + C 226 * X ^ 3 + C 199 * X ^ 4 + C 1137 * X ^ 5 + C 1163 * X ^ 6 + C 780 * X ^ 7 + C 1163 * X ^ 8 + C 617 * X ^ 9
theorem tstep0 : Atstep0 * Btstep0 = S2550F10 * Qtstep0 + Ntstep0 := by
  have hA : Atstep0.natDegree ≤ 9 := by unfold Atstep0; compute_degree!
  have hB : Btstep0.natDegree ≤ 9 := by unfold Btstep0; compute_degree!
  have hQ : Qtstep0.natDegree ≤ 8 := by unfold Qtstep0; compute_degree!
  have hN : Ntstep0.natDegree ≤ 9 := by unfold Ntstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Atstep0 * Btstep0).natDegree ≤ 18 := by
    calc (Atstep0 * Btstep0).natDegree ≤ Atstep0.natDegree + Btstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qtstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep0).natDegree ≤ S2550F10.natDegree + Qtstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qtstep0 + Ntstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep0 + Ntstep0).natDegree
        ≤ max (S2550F10 * Qtstep0).natDegree Ntstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Atstep0, Btstep0, Qtstep0, Ntstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Atstep1 : (ZMod 1249)[X] := C 428 + C 197 * X + C 164 * X ^ 2 + C 226 * X ^ 3 + C 199 * X ^ 4 + C 1137 * X ^ 5 + C 1163 * X ^ 6 + C 780 * X ^ 7 + C 1163 * X ^ 8 + C 617 * X ^ 9
def Btstep1 : (ZMod 1249)[X] := C 317 + C 512 * X + C 819 * X ^ 2 + C 1154 * X ^ 3 + C 767 * X ^ 4 + C 1060 * X ^ 5 + C 1110 * X ^ 6 + C 701 * X ^ 7 + C 571 * X ^ 8 + C 172 * X ^ 9
def Qtstep1 : (ZMod 1249)[X] := C 362 + C 564 * X + C 581 * X ^ 2 + C 111 * X ^ 3 + C 845 * X ^ 4 + C 167 * X ^ 5 + C 1113 * X ^ 6 + C 1173 * X ^ 7 + C 1208 * X ^ 8
def Ntstep1 : (ZMod 1249)[X] := C 656 + C 538 * X + C 1242 * X ^ 2 + C 988 * X ^ 3 + C 45 * X ^ 4 + C 358 * X ^ 5 + C 395 * X ^ 6 + C 241 * X ^ 7 + C 245 * X ^ 8 + C 280 * X ^ 9
theorem tstep1 : Atstep1 * Btstep1 = S2550F10 * Qtstep1 + Ntstep1 := by
  have hA : Atstep1.natDegree ≤ 9 := by unfold Atstep1; compute_degree!
  have hB : Btstep1.natDegree ≤ 9 := by unfold Btstep1; compute_degree!
  have hQ : Qtstep1.natDegree ≤ 8 := by unfold Qtstep1; compute_degree!
  have hN : Ntstep1.natDegree ≤ 9 := by unfold Ntstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Atstep1 * Btstep1).natDegree ≤ 18 := by
    calc (Atstep1 * Btstep1).natDegree ≤ Atstep1.natDegree + Btstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qtstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep1).natDegree ≤ S2550F10.natDegree + Qtstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qtstep1 + Ntstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep1 + Ntstep1).natDegree
        ≤ max (S2550F10 * Qtstep1).natDegree Ntstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Atstep1, Btstep1, Qtstep1, Ntstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Atstep2 : (ZMod 1249)[X] := C 656 + C 538 * X + C 1242 * X ^ 2 + C 988 * X ^ 3 + C 45 * X ^ 4 + C 358 * X ^ 5 + C 395 * X ^ 6 + C 241 * X ^ 7 + C 245 * X ^ 8 + C 280 * X ^ 9
def Btstep2 : (ZMod 1249)[X] := C 1060 + C 957 * X + C 591 * X ^ 2 + C 766 * X ^ 3 + C 816 * X ^ 4 + C 315 * X ^ 5 + C 752 * X ^ 6 + C 499 * X ^ 7 + C 317 * X ^ 8 + C 847 * X ^ 9
def Qtstep2 : (ZMod 1249)[X] := C 513 + C 383 * X + C 460 * X ^ 2 + C 820 * X ^ 3 + C 108 * X ^ 4 + C 945 * X ^ 5 + C 1018 * X ^ 6 + C 830 * X ^ 7 + C 1099 * X ^ 8
def Ntstep2 : (ZMod 1249)[X] := C 638 + C 237 * X + C 462 * X ^ 2 + C 445 * X ^ 3 + C 530 * X ^ 4 + C 386 * X ^ 5 + C 1217 * X ^ 6 + C 766 * X ^ 7 + C 682 * X ^ 8 + C 825 * X ^ 9
theorem tstep2 : Atstep2 * Btstep2 = S2550F10 * Qtstep2 + Ntstep2 := by
  have hA : Atstep2.natDegree ≤ 9 := by unfold Atstep2; compute_degree!
  have hB : Btstep2.natDegree ≤ 9 := by unfold Btstep2; compute_degree!
  have hQ : Qtstep2.natDegree ≤ 8 := by unfold Qtstep2; compute_degree!
  have hN : Ntstep2.natDegree ≤ 9 := by unfold Ntstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Atstep2 * Btstep2).natDegree ≤ 18 := by
    calc (Atstep2 * Btstep2).natDegree ≤ Atstep2.natDegree + Btstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qtstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep2).natDegree ≤ S2550F10.natDegree + Qtstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qtstep2 + Ntstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep2 + Ntstep2).natDegree
        ≤ max (S2550F10 * Qtstep2).natDegree Ntstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Atstep2, Btstep2, Qtstep2, Ntstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Atstep3 : (ZMod 1249)[X] := C 638 + C 237 * X + C 462 * X ^ 2 + C 445 * X ^ 3 + C 530 * X ^ 4 + C 386 * X ^ 5 + C 1217 * X ^ 6 + C 766 * X ^ 7 + C 682 * X ^ 8 + C 825 * X ^ 9
def Btstep3 : (ZMod 1249)[X] := C 1 * X
def Qtstep3 : (ZMod 1249)[X] := C 825
def Ntstep3 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
theorem tstep3 : Atstep3 * Btstep3 = S2550F10 * Qtstep3 + Ntstep3 := by
  have hA : Atstep3.natDegree ≤ 9 := by unfold Atstep3; compute_degree!
  have hB : Btstep3.natDegree ≤ 9 := by unfold Btstep3; compute_degree!
  have hQ : Qtstep3.natDegree ≤ 8 := by unfold Qtstep3; compute_degree!
  have hN : Ntstep3.natDegree ≤ 9 := by unfold Ntstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Atstep3 * Btstep3).natDegree ≤ 18 := by
    calc (Atstep3 * Btstep3).natDegree ≤ Atstep3.natDegree + Btstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qtstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep3).natDegree ≤ S2550F10.natDegree + Qtstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qtstep3 + Ntstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qtstep3 + Ntstep3).natDegree
        ≤ max (S2550F10 * Qtstep3).natDegree Ntstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Atstep3, Btstep3, Qtstep3, Ntstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def U0 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
def U1 : (ZMod 1249)[X] := C 156 + C 1212 * X + C 1106 * X ^ 2 + C 284 * X ^ 3 + C 796 * X ^ 4 + C 718 * X ^ 5 + C 704 * X ^ 6 + C 923 * X ^ 7 + C 967 * X ^ 8 + C 101 * X ^ 9
def U2 : (ZMod 1249)[X] := C 714 + C 462 * X + C 285 * X ^ 2 + C 530 * X ^ 3 + C 1007 * X ^ 4 + C 237 * X ^ 5 + C 188 * X ^ 6 + C 155 * X ^ 7 + C 1112 * X ^ 8 + C 701 * X ^ 9
def U3 : (ZMod 1249)[X] := C 584 + C 1032 * X + C 478 * X ^ 2 + C 194 * X ^ 3 + C 155 * X ^ 4 + C 1014 * X ^ 5 + C 1239 * X ^ 6 + C 1217 * X ^ 7 + C 1020 * X ^ 8 + C 623 * X ^ 9
def U4 : (ZMod 1249)[X] := C 267 + C 967 * X + C 309 * X ^ 2 + C 550 * X ^ 3 + C 1179 * X ^ 4 + C 612 * X ^ 5 + C 578 * X ^ 6 + C 1038 * X ^ 7 + C 316 * X ^ 8 + C 286 * X ^ 9
def U5 : (ZMod 1249)[X] := C 1156 + C 41 * X + C 615 * X ^ 2 + C 231 * X ^ 3 + C 400 * X ^ 4 + C 609 * X ^ 5 + C 1080 * X ^ 6 + C 791 * X ^ 7 + C 1220 * X ^ 8 + C 1015 * X ^ 9
def U6 : (ZMod 1249)[X] := C 1173 + C 570 * X + C 176 * X ^ 2 + C 825 * X ^ 3 + C 1243 * X ^ 4 + C 672 * X ^ 5 + C 1150 * X ^ 6 + C 696 * X ^ 7 + C 985 * X ^ 8 + C 419 * X ^ 9
def U7 : (ZMod 1249)[X] := C 366 + C 858 * X + C 152 * X ^ 2 + C 1007 * X ^ 3 + C 685 * X ^ 4 + C 421 * X ^ 5 + C 74 * X ^ 6 + C 523 * X ^ 7 + C 568 * X ^ 8 + C 954 * X ^ 9
def U8 : (ZMod 1249)[X] := C 432 + C 972 * X + C 137 * X ^ 2 + C 956 * X ^ 3 + C 339 * X ^ 4 + C 518 * X ^ 5 + C 380 * X ^ 6 + C 648 * X ^ 7 + C 112 * X ^ 8 + C 834 * X ^ 9
def U9 : (ZMod 1249)[X] := C 555 + C 872 * X + C 144 * X ^ 2 + C 685 * X ^ 3 + C 1068 * X ^ 4 + C 107 * X ^ 5 + C 862 * X ^ 6 + C 1151 * X ^ 7 + C 642 * X ^ 8 + C 775 * X ^ 9
def U10 : (ZMod 1249)[X] := C 644 + C 889 * X + C 20 * X ^ 2 + C 552 * X ^ 3 + C 1015 * X ^ 4 + C 1199 * X ^ 5 + C 1208 * X ^ 6 + C 524 * X ^ 7 + C 407 * X ^ 8 + C 264 * X ^ 9
def Austep0 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
def Bustep0 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
def Qustep0 : (ZMod 1249)[X] := C 855 + C 314 * X + C 148 * X ^ 2 + C 423 * X ^ 3 + C 755 * X ^ 4 + C 878 * X ^ 5 + C 322 * X ^ 6 + C 668 * X ^ 7 + C 638 * X ^ 8
def Nustep0 : (ZMod 1249)[X] := C 156 + C 1212 * X + C 1106 * X ^ 2 + C 284 * X ^ 3 + C 796 * X ^ 4 + C 718 * X ^ 5 + C 704 * X ^ 6 + C 923 * X ^ 7 + C 967 * X ^ 8 + C 101 * X ^ 9
theorem ustep0 : Austep0 * Bustep0 = S2550F10 * Qustep0 + Nustep0 := by
  have hA : Austep0.natDegree ≤ 9 := by unfold Austep0; compute_degree!
  have hB : Bustep0.natDegree ≤ 9 := by unfold Bustep0; compute_degree!
  have hQ : Qustep0.natDegree ≤ 8 := by unfold Qustep0; compute_degree!
  have hN : Nustep0.natDegree ≤ 9 := by unfold Nustep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep0 * Bustep0).natDegree ≤ 18 := by
    calc (Austep0 * Bustep0).natDegree ≤ Austep0.natDegree + Bustep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep0).natDegree ≤ S2550F10.natDegree + Qustep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep0 + Nustep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep0 + Nustep0).natDegree
        ≤ max (S2550F10 * Qustep0).natDegree Nustep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep0, Bustep0, Qustep0, Nustep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep1 : (ZMod 1249)[X] := C 156 + C 1212 * X + C 1106 * X ^ 2 + C 284 * X ^ 3 + C 796 * X ^ 4 + C 718 * X ^ 5 + C 704 * X ^ 6 + C 923 * X ^ 7 + C 967 * X ^ 8 + C 101 * X ^ 9
def Bustep1 : (ZMod 1249)[X] := C 156 + C 1212 * X + C 1106 * X ^ 2 + C 284 * X ^ 3 + C 796 * X ^ 4 + C 718 * X ^ 5 + C 704 * X ^ 6 + C 923 * X ^ 7 + C 967 * X ^ 8 + C 101 * X ^ 9
def Qustep1 : (ZMod 1249)[X] := C 648 + C 582 * X + C 730 * X ^ 2 + C 1114 * X ^ 3 + C 735 * X ^ 4 + C 85 * X ^ 5 + C 486 * X ^ 6 + C 15 * X ^ 7 + C 209 * X ^ 8
def Nustep1 : (ZMod 1249)[X] := C 714 + C 462 * X + C 285 * X ^ 2 + C 530 * X ^ 3 + C 1007 * X ^ 4 + C 237 * X ^ 5 + C 188 * X ^ 6 + C 155 * X ^ 7 + C 1112 * X ^ 8 + C 701 * X ^ 9
theorem ustep1 : Austep1 * Bustep1 = S2550F10 * Qustep1 + Nustep1 := by
  have hA : Austep1.natDegree ≤ 9 := by unfold Austep1; compute_degree!
  have hB : Bustep1.natDegree ≤ 9 := by unfold Bustep1; compute_degree!
  have hQ : Qustep1.natDegree ≤ 8 := by unfold Qustep1; compute_degree!
  have hN : Nustep1.natDegree ≤ 9 := by unfold Nustep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep1 * Bustep1).natDegree ≤ 18 := by
    calc (Austep1 * Bustep1).natDegree ≤ Austep1.natDegree + Bustep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep1).natDegree ≤ S2550F10.natDegree + Qustep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep1 + Nustep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep1 + Nustep1).natDegree
        ≤ max (S2550F10 * Qustep1).natDegree Nustep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep1, Bustep1, Qustep1, Nustep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep2 : (ZMod 1249)[X] := C 714 + C 462 * X + C 285 * X ^ 2 + C 530 * X ^ 3 + C 1007 * X ^ 4 + C 237 * X ^ 5 + C 188 * X ^ 6 + C 155 * X ^ 7 + C 1112 * X ^ 8 + C 701 * X ^ 9
def Bustep2 : (ZMod 1249)[X] := C 714 + C 462 * X + C 285 * X ^ 2 + C 530 * X ^ 3 + C 1007 * X ^ 4 + C 237 * X ^ 5 + C 188 * X ^ 6 + C 155 * X ^ 7 + C 1112 * X ^ 8 + C 701 * X ^ 9
def Qustep2 : (ZMod 1249)[X] := C 1033 + C 250 * X + C 583 * X ^ 2 + C 495 * X ^ 3 + C 628 * X ^ 4 + C 495 * X ^ 5 + C 909 * X ^ 6 + C 1193 * X ^ 7 + C 544 * X ^ 8
def Nustep2 : (ZMod 1249)[X] := C 584 + C 1032 * X + C 478 * X ^ 2 + C 194 * X ^ 3 + C 155 * X ^ 4 + C 1014 * X ^ 5 + C 1239 * X ^ 6 + C 1217 * X ^ 7 + C 1020 * X ^ 8 + C 623 * X ^ 9
theorem ustep2 : Austep2 * Bustep2 = S2550F10 * Qustep2 + Nustep2 := by
  have hA : Austep2.natDegree ≤ 9 := by unfold Austep2; compute_degree!
  have hB : Bustep2.natDegree ≤ 9 := by unfold Bustep2; compute_degree!
  have hQ : Qustep2.natDegree ≤ 8 := by unfold Qustep2; compute_degree!
  have hN : Nustep2.natDegree ≤ 9 := by unfold Nustep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep2 * Bustep2).natDegree ≤ 18 := by
    calc (Austep2 * Bustep2).natDegree ≤ Austep2.natDegree + Bustep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep2).natDegree ≤ S2550F10.natDegree + Qustep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep2 + Nustep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep2 + Nustep2).natDegree
        ≤ max (S2550F10 * Qustep2).natDegree Nustep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep2, Bustep2, Qustep2, Nustep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep3 : (ZMod 1249)[X] := C 584 + C 1032 * X + C 478 * X ^ 2 + C 194 * X ^ 3 + C 155 * X ^ 4 + C 1014 * X ^ 5 + C 1239 * X ^ 6 + C 1217 * X ^ 7 + C 1020 * X ^ 8 + C 623 * X ^ 9
def Bustep3 : (ZMod 1249)[X] := C 584 + C 1032 * X + C 478 * X ^ 2 + C 194 * X ^ 3 + C 155 * X ^ 4 + C 1014 * X ^ 5 + C 1239 * X ^ 6 + C 1217 * X ^ 7 + C 1020 * X ^ 8 + C 623 * X ^ 9
def Qustep3 : (ZMod 1249)[X] := C 327 + C 1029 * X + C 1112 * X ^ 2 + C 917 * X ^ 3 + C 575 * X ^ 4 + C 128 * X ^ 5 + C 758 * X ^ 6 + C 29 * X ^ 7 + C 939 * X ^ 8
def Nustep3 : (ZMod 1249)[X] := C 267 + C 967 * X + C 309 * X ^ 2 + C 550 * X ^ 3 + C 1179 * X ^ 4 + C 612 * X ^ 5 + C 578 * X ^ 6 + C 1038 * X ^ 7 + C 316 * X ^ 8 + C 286 * X ^ 9
theorem ustep3 : Austep3 * Bustep3 = S2550F10 * Qustep3 + Nustep3 := by
  have hA : Austep3.natDegree ≤ 9 := by unfold Austep3; compute_degree!
  have hB : Bustep3.natDegree ≤ 9 := by unfold Bustep3; compute_degree!
  have hQ : Qustep3.natDegree ≤ 8 := by unfold Qustep3; compute_degree!
  have hN : Nustep3.natDegree ≤ 9 := by unfold Nustep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep3 * Bustep3).natDegree ≤ 18 := by
    calc (Austep3 * Bustep3).natDegree ≤ Austep3.natDegree + Bustep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep3).natDegree ≤ S2550F10.natDegree + Qustep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep3 + Nustep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep3 + Nustep3).natDegree
        ≤ max (S2550F10 * Qustep3).natDegree Nustep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep3, Bustep3, Qustep3, Nustep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep4 : (ZMod 1249)[X] := C 267 + C 967 * X + C 309 * X ^ 2 + C 550 * X ^ 3 + C 1179 * X ^ 4 + C 612 * X ^ 5 + C 578 * X ^ 6 + C 1038 * X ^ 7 + C 316 * X ^ 8 + C 286 * X ^ 9
def Bustep4 : (ZMod 1249)[X] := C 267 + C 967 * X + C 309 * X ^ 2 + C 550 * X ^ 3 + C 1179 * X ^ 4 + C 612 * X ^ 5 + C 578 * X ^ 6 + C 1038 * X ^ 7 + C 316 * X ^ 8 + C 286 * X ^ 9
def Qustep4 : (ZMod 1249)[X] := C 515 + C 1124 * X + C 1006 * X ^ 2 + C 840 * X ^ 3 + C 664 * X ^ 4 + C 1006 * X ^ 5 + C 20 * X ^ 6 + C 1097 * X ^ 7 + C 611 * X ^ 8
def Nustep4 : (ZMod 1249)[X] := C 1156 + C 41 * X + C 615 * X ^ 2 + C 231 * X ^ 3 + C 400 * X ^ 4 + C 609 * X ^ 5 + C 1080 * X ^ 6 + C 791 * X ^ 7 + C 1220 * X ^ 8 + C 1015 * X ^ 9
theorem ustep4 : Austep4 * Bustep4 = S2550F10 * Qustep4 + Nustep4 := by
  have hA : Austep4.natDegree ≤ 9 := by unfold Austep4; compute_degree!
  have hB : Bustep4.natDegree ≤ 9 := by unfold Bustep4; compute_degree!
  have hQ : Qustep4.natDegree ≤ 8 := by unfold Qustep4; compute_degree!
  have hN : Nustep4.natDegree ≤ 9 := by unfold Nustep4; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep4 * Bustep4).natDegree ≤ 18 := by
    calc (Austep4 * Bustep4).natDegree ≤ Austep4.natDegree + Bustep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep4).natDegree ≤ S2550F10.natDegree + Qustep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep4 + Nustep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep4 + Nustep4).natDegree
        ≤ max (S2550F10 * Qustep4).natDegree Nustep4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep4, Bustep4, Qustep4, Nustep4, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep5 : (ZMod 1249)[X] := C 1156 + C 41 * X + C 615 * X ^ 2 + C 231 * X ^ 3 + C 400 * X ^ 4 + C 609 * X ^ 5 + C 1080 * X ^ 6 + C 791 * X ^ 7 + C 1220 * X ^ 8 + C 1015 * X ^ 9
def Bustep5 : (ZMod 1249)[X] := C 1156 + C 41 * X + C 615 * X ^ 2 + C 231 * X ^ 3 + C 400 * X ^ 4 + C 609 * X ^ 5 + C 1080 * X ^ 6 + C 791 * X ^ 7 + C 1220 * X ^ 8 + C 1015 * X ^ 9
def Qustep5 : (ZMod 1249)[X] := C 1081 + C 189 * X + C 1108 * X ^ 2 + C 78 * X ^ 3 + C 649 * X ^ 4 + C 542 * X ^ 5 + C 878 * X ^ 6 + C 174 * X ^ 7 + C 1049 * X ^ 8
def Nustep5 : (ZMod 1249)[X] := C 1173 + C 570 * X + C 176 * X ^ 2 + C 825 * X ^ 3 + C 1243 * X ^ 4 + C 672 * X ^ 5 + C 1150 * X ^ 6 + C 696 * X ^ 7 + C 985 * X ^ 8 + C 419 * X ^ 9
theorem ustep5 : Austep5 * Bustep5 = S2550F10 * Qustep5 + Nustep5 := by
  have hA : Austep5.natDegree ≤ 9 := by unfold Austep5; compute_degree!
  have hB : Bustep5.natDegree ≤ 9 := by unfold Bustep5; compute_degree!
  have hQ : Qustep5.natDegree ≤ 8 := by unfold Qustep5; compute_degree!
  have hN : Nustep5.natDegree ≤ 9 := by unfold Nustep5; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep5 * Bustep5).natDegree ≤ 18 := by
    calc (Austep5 * Bustep5).natDegree ≤ Austep5.natDegree + Bustep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep5).natDegree ≤ S2550F10.natDegree + Qustep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep5 + Nustep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep5 + Nustep5).natDegree
        ≤ max (S2550F10 * Qustep5).natDegree Nustep5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep5, Bustep5, Qustep5, Nustep5, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep6 : (ZMod 1249)[X] := C 1173 + C 570 * X + C 176 * X ^ 2 + C 825 * X ^ 3 + C 1243 * X ^ 4 + C 672 * X ^ 5 + C 1150 * X ^ 6 + C 696 * X ^ 7 + C 985 * X ^ 8 + C 419 * X ^ 9
def Bustep6 : (ZMod 1249)[X] := C 1173 + C 570 * X + C 176 * X ^ 2 + C 825 * X ^ 3 + C 1243 * X ^ 4 + C 672 * X ^ 5 + C 1150 * X ^ 6 + C 696 * X ^ 7 + C 985 * X ^ 8 + C 419 * X ^ 9
def Qustep6 : (ZMod 1249)[X] := C 117 + C 31 * X + C 58 * X ^ 2 + C 404 * X ^ 3 + C 195 * X ^ 4 + C 545 * X ^ 5 + C 743 * X ^ 6 + C 1200 * X ^ 7 + C 701 * X ^ 8
def Nustep6 : (ZMod 1249)[X] := C 366 + C 858 * X + C 152 * X ^ 2 + C 1007 * X ^ 3 + C 685 * X ^ 4 + C 421 * X ^ 5 + C 74 * X ^ 6 + C 523 * X ^ 7 + C 568 * X ^ 8 + C 954 * X ^ 9
theorem ustep6 : Austep6 * Bustep6 = S2550F10 * Qustep6 + Nustep6 := by
  have hA : Austep6.natDegree ≤ 9 := by unfold Austep6; compute_degree!
  have hB : Bustep6.natDegree ≤ 9 := by unfold Bustep6; compute_degree!
  have hQ : Qustep6.natDegree ≤ 8 := by unfold Qustep6; compute_degree!
  have hN : Nustep6.natDegree ≤ 9 := by unfold Nustep6; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep6 * Bustep6).natDegree ≤ 18 := by
    calc (Austep6 * Bustep6).natDegree ≤ Austep6.natDegree + Bustep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep6).natDegree ≤ S2550F10.natDegree + Qustep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep6 + Nustep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep6 + Nustep6).natDegree
        ≤ max (S2550F10 * Qustep6).natDegree Nustep6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep6, Bustep6, Qustep6, Nustep6, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep7 : (ZMod 1249)[X] := C 366 + C 858 * X + C 152 * X ^ 2 + C 1007 * X ^ 3 + C 685 * X ^ 4 + C 421 * X ^ 5 + C 74 * X ^ 6 + C 523 * X ^ 7 + C 568 * X ^ 8 + C 954 * X ^ 9
def Bustep7 : (ZMod 1249)[X] := C 366 + C 858 * X + C 152 * X ^ 2 + C 1007 * X ^ 3 + C 685 * X ^ 4 + C 421 * X ^ 5 + C 74 * X ^ 6 + C 523 * X ^ 7 + C 568 * X ^ 8 + C 954 * X ^ 9
def Qustep7 : (ZMod 1249)[X] := C 971 + C 196 * X + C 222 * X ^ 2 + C 572 * X ^ 3 + C 948 * X ^ 4 + C 1065 * X ^ 5 + C 450 * X ^ 6 + C 646 * X ^ 7 + C 844 * X ^ 8
def Nustep7 : (ZMod 1249)[X] := C 432 + C 972 * X + C 137 * X ^ 2 + C 956 * X ^ 3 + C 339 * X ^ 4 + C 518 * X ^ 5 + C 380 * X ^ 6 + C 648 * X ^ 7 + C 112 * X ^ 8 + C 834 * X ^ 9
theorem ustep7 : Austep7 * Bustep7 = S2550F10 * Qustep7 + Nustep7 := by
  have hA : Austep7.natDegree ≤ 9 := by unfold Austep7; compute_degree!
  have hB : Bustep7.natDegree ≤ 9 := by unfold Bustep7; compute_degree!
  have hQ : Qustep7.natDegree ≤ 8 := by unfold Qustep7; compute_degree!
  have hN : Nustep7.natDegree ≤ 9 := by unfold Nustep7; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep7 * Bustep7).natDegree ≤ 18 := by
    calc (Austep7 * Bustep7).natDegree ≤ Austep7.natDegree + Bustep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep7).natDegree ≤ S2550F10.natDegree + Qustep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep7 + Nustep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep7 + Nustep7).natDegree
        ≤ max (S2550F10 * Qustep7).natDegree Nustep7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep7, Bustep7, Qustep7, Nustep7, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep8 : (ZMod 1249)[X] := C 432 + C 972 * X + C 137 * X ^ 2 + C 956 * X ^ 3 + C 339 * X ^ 4 + C 518 * X ^ 5 + C 380 * X ^ 6 + C 648 * X ^ 7 + C 112 * X ^ 8 + C 834 * X ^ 9
def Bustep8 : (ZMod 1249)[X] := C 432 + C 972 * X + C 137 * X ^ 2 + C 956 * X ^ 3 + C 339 * X ^ 4 + C 518 * X ^ 5 + C 380 * X ^ 6 + C 648 * X ^ 7 + C 112 * X ^ 8 + C 834 * X ^ 9
def Qustep8 : (ZMod 1249)[X] := C 534 + C 415 * X + C 835 * X ^ 2 + C 1020 * X ^ 3 + C 455 * X ^ 4 + C 1148 * X ^ 5 + C 238 * X ^ 6 + C 118 * X ^ 7 + C 1112 * X ^ 8
def Nustep8 : (ZMod 1249)[X] := C 555 + C 872 * X + C 144 * X ^ 2 + C 685 * X ^ 3 + C 1068 * X ^ 4 + C 107 * X ^ 5 + C 862 * X ^ 6 + C 1151 * X ^ 7 + C 642 * X ^ 8 + C 775 * X ^ 9
theorem ustep8 : Austep8 * Bustep8 = S2550F10 * Qustep8 + Nustep8 := by
  have hA : Austep8.natDegree ≤ 9 := by unfold Austep8; compute_degree!
  have hB : Bustep8.natDegree ≤ 9 := by unfold Bustep8; compute_degree!
  have hQ : Qustep8.natDegree ≤ 8 := by unfold Qustep8; compute_degree!
  have hN : Nustep8.natDegree ≤ 9 := by unfold Nustep8; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep8 * Bustep8).natDegree ≤ 18 := by
    calc (Austep8 * Bustep8).natDegree ≤ Austep8.natDegree + Bustep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep8).natDegree ≤ S2550F10.natDegree + Qustep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep8 + Nustep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep8 + Nustep8).natDegree
        ≤ max (S2550F10 * Qustep8).natDegree Nustep8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep8, Bustep8, Qustep8, Nustep8, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Austep9 : (ZMod 1249)[X] := C 555 + C 872 * X + C 144 * X ^ 2 + C 685 * X ^ 3 + C 1068 * X ^ 4 + C 107 * X ^ 5 + C 862 * X ^ 6 + C 1151 * X ^ 7 + C 642 * X ^ 8 + C 775 * X ^ 9
def Bustep9 : (ZMod 1249)[X] := C 555 + C 872 * X + C 144 * X ^ 2 + C 685 * X ^ 3 + C 1068 * X ^ 4 + C 107 * X ^ 5 + C 862 * X ^ 6 + C 1151 * X ^ 7 + C 642 * X ^ 8 + C 775 * X ^ 9
def Qustep9 : (ZMod 1249)[X] := C 769 + C 41 * X + C 980 * X ^ 2 + C 191 * X ^ 3 + C 150 * X ^ 4 + C 964 * X ^ 5 + C 277 * X ^ 6 + C 542 * X ^ 7 + C 1105 * X ^ 8
def Nustep9 : (ZMod 1249)[X] := C 644 + C 889 * X + C 20 * X ^ 2 + C 552 * X ^ 3 + C 1015 * X ^ 4 + C 1199 * X ^ 5 + C 1208 * X ^ 6 + C 524 * X ^ 7 + C 407 * X ^ 8 + C 264 * X ^ 9
theorem ustep9 : Austep9 * Bustep9 = S2550F10 * Qustep9 + Nustep9 := by
  have hA : Austep9.natDegree ≤ 9 := by unfold Austep9; compute_degree!
  have hB : Bustep9.natDegree ≤ 9 := by unfold Bustep9; compute_degree!
  have hQ : Qustep9.natDegree ≤ 8 := by unfold Qustep9; compute_degree!
  have hN : Nustep9.natDegree ≤ 9 := by unfold Nustep9; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Austep9 * Bustep9).natDegree ≤ 18 := by
    calc (Austep9 * Bustep9).natDegree ≤ Austep9.natDegree + Bustep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qustep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep9).natDegree ≤ S2550F10.natDegree + Qustep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qustep9 + Nustep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qustep9 + Nustep9).natDegree
        ≤ max (S2550F10 * Qustep9).natDegree Nustep9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Austep9, Bustep9, Qustep9, Nustep9, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual

end