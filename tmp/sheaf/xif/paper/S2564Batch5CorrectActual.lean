import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

def C0 : (ZMod 1249)[X] := C 794 + C 903 * X + C 1242 * X ^ 2 + C 100 * X ^ 3 + C 526 * X ^ 4 + C 715 * X ^ 5 + C 798 * X ^ 6 + C 237 * X ^ 7 + C 993 * X ^ 8 + C 685 * X ^ 9
def C1 : (ZMod 1249)[X] := C 224 + C 544 * X + C 149 * X ^ 2 + C 451 * X ^ 3 + C 508 * X ^ 4 + C 600 * X ^ 5 + C 1216 * X ^ 6 + C 283 * X ^ 7 + C 347 * X ^ 8 + C 478 * X ^ 9
def C2 : (ZMod 1249)[X] := C 1144 + C 350 * X + C 590 * X ^ 2 + C 873 * X ^ 3 + C 1146 * X ^ 4 + C 908 * X ^ 5 + C 540 * X ^ 6 + C 905 * X ^ 7 + C 826 * X ^ 8 + C 1245 * X ^ 9
def C3 : (ZMod 1249)[X] := C 466 + C 107 * X + C 355 * X ^ 2 + C 770 * X ^ 3 + C 375 * X ^ 4 + C 459 * X ^ 5 + C 698 * X ^ 6 + C 283 * X ^ 7 + C 982 * X ^ 8 + C 685 * X ^ 9
def C4 : (ZMod 1249)[X] := C 762 + C 335 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
def Acstep0 : (ZMod 1249)[X] := C 794 + C 903 * X + C 1242 * X ^ 2 + C 100 * X ^ 3 + C 526 * X ^ 4 + C 715 * X ^ 5 + C 798 * X ^ 6 + C 237 * X ^ 7 + C 993 * X ^ 8 + C 685 * X ^ 9
def Bcstep0 : (ZMod 1249)[X] := C 676 + C 215 * X + C 455 * X ^ 2 + C 724 * X ^ 3 + C 116 * X ^ 4 + C 1068 * X ^ 5 + C 159 * X ^ 6 + C 176 * X ^ 7 + C 858 * X ^ 8 + C 1132 * X ^ 9
def Qcstep0 : (ZMod 1249)[X] := C 279 + C 17 * X + C 413 * X ^ 2 + C 102 * X ^ 3 + C 378 * X ^ 4 + C 336 * X ^ 5 + C 1125 * X ^ 6 + C 1151 * X ^ 7 + C 1040 * X ^ 8
def Ncstep0 : (ZMod 1249)[X] := C 224 + C 544 * X + C 149 * X ^ 2 + C 451 * X ^ 3 + C 508 * X ^ 4 + C 600 * X ^ 5 + C 1216 * X ^ 6 + C 283 * X ^ 7 + C 347 * X ^ 8 + C 478 * X ^ 9
theorem cstep0 : Acstep0 * Bcstep0 = S2550F10 * Qcstep0 + Ncstep0 := by
  have hA : Acstep0.natDegree ≤ 9 := by unfold Acstep0; compute_degree!
  have hB : Bcstep0.natDegree ≤ 9 := by unfold Bcstep0; compute_degree!
  have hQ : Qcstep0.natDegree ≤ 8 := by unfold Qcstep0; compute_degree!
  have hN : Ncstep0.natDegree ≤ 9 := by unfold Ncstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Acstep0 * Bcstep0).natDegree ≤ 18 := by
    calc (Acstep0 * Bcstep0).natDegree ≤ Acstep0.natDegree + Bcstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qcstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep0).natDegree ≤ S2550F10.natDegree + Qcstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qcstep0 + Ncstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep0 + Ncstep0).natDegree
        ≤ max (S2550F10 * Qcstep0).natDegree Ncstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Acstep0, Bcstep0, Qcstep0, Ncstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Acstep1 : (ZMod 1249)[X] := C 224 + C 544 * X + C 149 * X ^ 2 + C 451 * X ^ 3 + C 508 * X ^ 4 + C 600 * X ^ 5 + C 1216 * X ^ 6 + C 283 * X ^ 7 + C 347 * X ^ 8 + C 478 * X ^ 9
def Bcstep1 : (ZMod 1249)[X] := C 1179 + C 590 * X + C 958 * X ^ 2 + C 616 * X ^ 3 + C 785 * X ^ 4 + C 340 * X ^ 5 + C 668 * X ^ 6 + C 821 * X ^ 7 + C 525 * X ^ 8 + C 556 * X ^ 9
def Qcstep1 : (ZMod 1249)[X] := C 350 + C 729 * X + C 563 * X ^ 2 + C 583 * X ^ 3 + C 367 * X ^ 4 + C 729 * X ^ 5 + C 359 * X ^ 6 + C 190 * X ^ 7 + C 980 * X ^ 8
def Ncstep1 : (ZMod 1249)[X] := C 1144 + C 350 * X + C 590 * X ^ 2 + C 873 * X ^ 3 + C 1146 * X ^ 4 + C 908 * X ^ 5 + C 540 * X ^ 6 + C 905 * X ^ 7 + C 826 * X ^ 8 + C 1245 * X ^ 9
theorem cstep1 : Acstep1 * Bcstep1 = S2550F10 * Qcstep1 + Ncstep1 := by
  have hA : Acstep1.natDegree ≤ 9 := by unfold Acstep1; compute_degree!
  have hB : Bcstep1.natDegree ≤ 9 := by unfold Bcstep1; compute_degree!
  have hQ : Qcstep1.natDegree ≤ 8 := by unfold Qcstep1; compute_degree!
  have hN : Ncstep1.natDegree ≤ 9 := by unfold Ncstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Acstep1 * Bcstep1).natDegree ≤ 18 := by
    calc (Acstep1 * Bcstep1).natDegree ≤ Acstep1.natDegree + Bcstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qcstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep1).natDegree ≤ S2550F10.natDegree + Qcstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qcstep1 + Ncstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep1 + Ncstep1).natDegree
        ≤ max (S2550F10 * Qcstep1).natDegree Ncstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Acstep1, Bcstep1, Qcstep1, Ncstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Acstep2 : (ZMod 1249)[X] := C 1144 + C 350 * X + C 590 * X ^ 2 + C 873 * X ^ 3 + C 1146 * X ^ 4 + C 908 * X ^ 5 + C 540 * X ^ 6 + C 905 * X ^ 7 + C 826 * X ^ 8 + C 1245 * X ^ 9
def Bcstep2 : (ZMod 1249)[X] := C 364 + C 743 * X + C 643 * X ^ 2 + C 733 * X ^ 3 + C 770 * X ^ 4 + C 564 * X ^ 5 + C 85 * X ^ 6 + C 785 * X ^ 7 + C 1017 * X ^ 8 + C 523 * X ^ 9
def Qcstep2 : (ZMod 1249)[X] := C 308 + C 1052 * X + C 558 * X ^ 2 + C 1086 * X ^ 3 + C 401 * X ^ 4 + C 901 * X ^ 5 + C 168 * X ^ 6 + C 417 * X ^ 7 + C 406 * X ^ 8
def Ncstep2 : (ZMod 1249)[X] := C 466 + C 107 * X + C 355 * X ^ 2 + C 770 * X ^ 3 + C 375 * X ^ 4 + C 459 * X ^ 5 + C 698 * X ^ 6 + C 283 * X ^ 7 + C 982 * X ^ 8 + C 685 * X ^ 9
theorem cstep2 : Acstep2 * Bcstep2 = S2550F10 * Qcstep2 + Ncstep2 := by
  have hA : Acstep2.natDegree ≤ 9 := by unfold Acstep2; compute_degree!
  have hB : Bcstep2.natDegree ≤ 9 := by unfold Bcstep2; compute_degree!
  have hQ : Qcstep2.natDegree ≤ 8 := by unfold Qcstep2; compute_degree!
  have hN : Ncstep2.natDegree ≤ 9 := by unfold Ncstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Acstep2 * Bcstep2).natDegree ≤ 18 := by
    calc (Acstep2 * Bcstep2).natDegree ≤ Acstep2.natDegree + Bcstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qcstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep2).natDegree ≤ S2550F10.natDegree + Qcstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qcstep2 + Ncstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep2 + Ncstep2).natDegree
        ≤ max (S2550F10 * Qcstep2).natDegree Ncstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Acstep2, Bcstep2, Qcstep2, Ncstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Acstep3 : (ZMod 1249)[X] := C 466 + C 107 * X + C 355 * X ^ 2 + C 770 * X ^ 3 + C 375 * X ^ 4 + C 459 * X ^ 5 + C 698 * X ^ 6 + C 283 * X ^ 7 + C 982 * X ^ 8 + C 685 * X ^ 9
def Bcstep3 : (ZMod 1249)[X] := C 352 + C 513 * X + C 68 * X ^ 2 + C 465 * X ^ 3 + C 393 * X ^ 4 + C 933 * X ^ 5 + C 1104 * X ^ 6 + C 967 * X ^ 7 + C 1129 * X ^ 8 + C 713 * X ^ 9
def Qcstep3 : (ZMod 1249)[X] := C 906 + C 607 * X + C 463 * X ^ 2 + C 482 * X ^ 3 + C 211 * X ^ 4 + C 927 * X ^ 5 + C 297 * X ^ 6 + C 969 * X ^ 7 + C 46 * X ^ 8
def Ncstep3 : (ZMod 1249)[X] := C 762 + C 335 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
theorem cstep3 : Acstep3 * Bcstep3 = S2550F10 * Qcstep3 + Ncstep3 := by
  have hA : Acstep3.natDegree ≤ 9 := by unfold Acstep3; compute_degree!
  have hB : Bcstep3.natDegree ≤ 9 := by unfold Bcstep3; compute_degree!
  have hQ : Qcstep3.natDegree ≤ 8 := by unfold Qcstep3; compute_degree!
  have hN : Ncstep3.natDegree ≤ 9 := by unfold Ncstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Acstep3 * Bcstep3).natDegree ≤ 18 := by
    calc (Acstep3 * Bcstep3).natDegree ≤ Acstep3.natDegree + Bcstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qcstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep3).natDegree ≤ S2550F10.natDegree + Qcstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qcstep3 + Ncstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qcstep3 + Ncstep3).natDegree
        ≤ max (S2550F10 * Qcstep3).natDegree Ncstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Acstep3, Bcstep3, Qcstep3, Ncstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def D0 : (ZMod 1249)[X] := C 762 + C 335 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
def D1 : (ZMod 1249)[X] := C 882 + C 954 * X + C 79 * X ^ 2 + C 1113 * X ^ 3 + C 167 * X ^ 4 + C 679 * X ^ 5 + C 333 * X ^ 6 + C 1036 * X ^ 7 + C 1096 * X ^ 8 + C 665 * X ^ 9
def D2 : (ZMod 1249)[X] := C 894 + C 1132 * X + C 382 * X ^ 2 + C 426 * X ^ 3 + C 623 * X ^ 4 + C 468 * X ^ 5 + C 464 * X ^ 6 + C 75 * X ^ 7 + C 368 * X ^ 8 + C 238 * X ^ 9
def D3 : (ZMod 1249)[X] := C 713 + C 1165 * X + C 380 * X ^ 2 + C 942 * X ^ 3 + C 7 * X ^ 4 + C 652 * X ^ 5 + C 234 * X ^ 6 + C 845 * X ^ 7 + C 219 * X ^ 8 + C 411 * X ^ 9
def D4 : (ZMod 1249)[X] := C 366 + C 1096 * X + C 1209 * X ^ 2 + C 1248 * X ^ 3 + C 741 * X ^ 4 + C 789 * X ^ 5 + C 164 * X ^ 6 + C 585 * X ^ 7 + C 373 * X ^ 8 + C 126 * X ^ 9
def D5 : (ZMod 1249)[X] := C 374 + C 975 * X + C 97 * X ^ 2 + C 269 * X ^ 3 + C 381 * X ^ 4 + C 788 * X ^ 5 + C 349 * X ^ 6 + C 966 * X ^ 7 + C 1135 * X ^ 8 + C 940 * X ^ 9
def D6 : (ZMod 1249)[X] := C 449 + C 1142 * X + C 1059 * X ^ 2 + C 418 * X ^ 3 + C 206 * X ^ 4 + C 302 * X ^ 5 + C 477 * X ^ 6 + C 1019 * X ^ 7 + C 923 * X ^ 8 + C 420 * X ^ 9
def D7 : (ZMod 1249)[X] := C 342 + C 295 * X + C 534 * X ^ 2 + C 317 * X ^ 3 + C 1105 * X ^ 4 + C 189 * X ^ 5 + C 891 * X ^ 6 + C 819 * X ^ 7 + C 956 * X ^ 8 + C 667 * X ^ 9
def D8 : (ZMod 1249)[X] := C 896 + C 17 * X + C 668 * X ^ 2 + C 660 * X ^ 3 + C 472 * X ^ 4 + C 352 * X ^ 5 + C 863 * X ^ 6 + C 404 * X ^ 7 + C 356 * X ^ 8 + C 1075 * X ^ 9
def D9 : (ZMod 1249)[X] := C 124 + C 415 * X + C 501 * X ^ 2 + C 562 * X ^ 3 + C 686 * X ^ 4 + C 348 * X ^ 5 + C 1108 * X ^ 6 + C 428 * X ^ 7 + C 537 * X ^ 8 + C 111 * X ^ 9
def D10 : (ZMod 1249)[X] := C 1173 + C 266 * X + C 309 * X ^ 2 + C 1199 * X ^ 3 + C 260 * X ^ 4 + C 457 * X ^ 5 + C 906 * X ^ 6 + C 116 * X ^ 7 + C 548 * X ^ 8 + C 571 * X ^ 9
def Adstep0 : (ZMod 1249)[X] := C 762 + C 335 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
def Bdstep0 : (ZMod 1249)[X] := C 762 + C 335 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
def Qdstep0 : (ZMod 1249)[X] := C 444 + C 239 * X + C 1101 * X ^ 2 + C 451 * X ^ 3 + C 186 * X ^ 4 + C 937 * X ^ 5 + C 373 * X ^ 6 + C 696 * X ^ 7 + C 532 * X ^ 8
def Ndstep0 : (ZMod 1249)[X] := C 882 + C 954 * X + C 79 * X ^ 2 + C 1113 * X ^ 3 + C 167 * X ^ 4 + C 679 * X ^ 5 + C 333 * X ^ 6 + C 1036 * X ^ 7 + C 1096 * X ^ 8 + C 665 * X ^ 9
theorem dstep0 : Adstep0 * Bdstep0 = S2550F10 * Qdstep0 + Ndstep0 := by
  have hA : Adstep0.natDegree ≤ 9 := by unfold Adstep0; compute_degree!
  have hB : Bdstep0.natDegree ≤ 9 := by unfold Bdstep0; compute_degree!
  have hQ : Qdstep0.natDegree ≤ 8 := by unfold Qdstep0; compute_degree!
  have hN : Ndstep0.natDegree ≤ 9 := by unfold Ndstep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep0 * Bdstep0).natDegree ≤ 18 := by
    calc (Adstep0 * Bdstep0).natDegree ≤ Adstep0.natDegree + Bdstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep0).natDegree ≤ S2550F10.natDegree + Qdstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep0 + Ndstep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep0 + Ndstep0).natDegree
        ≤ max (S2550F10 * Qdstep0).natDegree Ndstep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep0, Bdstep0, Qdstep0, Ndstep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep1 : (ZMod 1249)[X] := C 882 + C 954 * X + C 79 * X ^ 2 + C 1113 * X ^ 3 + C 167 * X ^ 4 + C 679 * X ^ 5 + C 333 * X ^ 6 + C 1036 * X ^ 7 + C 1096 * X ^ 8 + C 665 * X ^ 9
def Bdstep1 : (ZMod 1249)[X] := C 882 + C 954 * X + C 79 * X ^ 2 + C 1113 * X ^ 3 + C 167 * X ^ 4 + C 679 * X ^ 5 + C 333 * X ^ 6 + C 1036 * X ^ 7 + C 1096 * X ^ 8 + C 665 * X ^ 9
def Qdstep1 : (ZMod 1249)[X] := C 586 + C 854 * X + C 1016 * X ^ 2 + C 199 * X ^ 3 + C 330 * X ^ 4 + C 243 * X ^ 5 + C 132 * X ^ 6 + C 31 * X ^ 7 + C 79 * X ^ 8
def Ndstep1 : (ZMod 1249)[X] := C 894 + C 1132 * X + C 382 * X ^ 2 + C 426 * X ^ 3 + C 623 * X ^ 4 + C 468 * X ^ 5 + C 464 * X ^ 6 + C 75 * X ^ 7 + C 368 * X ^ 8 + C 238 * X ^ 9
theorem dstep1 : Adstep1 * Bdstep1 = S2550F10 * Qdstep1 + Ndstep1 := by
  have hA : Adstep1.natDegree ≤ 9 := by unfold Adstep1; compute_degree!
  have hB : Bdstep1.natDegree ≤ 9 := by unfold Bdstep1; compute_degree!
  have hQ : Qdstep1.natDegree ≤ 8 := by unfold Qdstep1; compute_degree!
  have hN : Ndstep1.natDegree ≤ 9 := by unfold Ndstep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep1 * Bdstep1).natDegree ≤ 18 := by
    calc (Adstep1 * Bdstep1).natDegree ≤ Adstep1.natDegree + Bdstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep1).natDegree ≤ S2550F10.natDegree + Qdstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep1 + Ndstep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep1 + Ndstep1).natDegree
        ≤ max (S2550F10 * Qdstep1).natDegree Ndstep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep1, Bdstep1, Qdstep1, Ndstep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep2 : (ZMod 1249)[X] := C 894 + C 1132 * X + C 382 * X ^ 2 + C 426 * X ^ 3 + C 623 * X ^ 4 + C 468 * X ^ 5 + C 464 * X ^ 6 + C 75 * X ^ 7 + C 368 * X ^ 8 + C 238 * X ^ 9
def Bdstep2 : (ZMod 1249)[X] := C 894 + C 1132 * X + C 382 * X ^ 2 + C 426 * X ^ 3 + C 623 * X ^ 4 + C 468 * X ^ 5 + C 464 * X ^ 6 + C 75 * X ^ 7 + C 368 * X ^ 8 + C 238 * X ^ 9
def Qdstep2 : (ZMod 1249)[X] := C 931 + C 1057 * X + C 376 * X ^ 2 + C 836 * X ^ 3 + C 764 * X ^ 4 + C 703 * X ^ 5 + C 656 * X ^ 6 + C 1127 * X ^ 7 + C 439 * X ^ 8
def Ndstep2 : (ZMod 1249)[X] := C 713 + C 1165 * X + C 380 * X ^ 2 + C 942 * X ^ 3 + C 7 * X ^ 4 + C 652 * X ^ 5 + C 234 * X ^ 6 + C 845 * X ^ 7 + C 219 * X ^ 8 + C 411 * X ^ 9
theorem dstep2 : Adstep2 * Bdstep2 = S2550F10 * Qdstep2 + Ndstep2 := by
  have hA : Adstep2.natDegree ≤ 9 := by unfold Adstep2; compute_degree!
  have hB : Bdstep2.natDegree ≤ 9 := by unfold Bdstep2; compute_degree!
  have hQ : Qdstep2.natDegree ≤ 8 := by unfold Qdstep2; compute_degree!
  have hN : Ndstep2.natDegree ≤ 9 := by unfold Ndstep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep2 * Bdstep2).natDegree ≤ 18 := by
    calc (Adstep2 * Bdstep2).natDegree ≤ Adstep2.natDegree + Bdstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep2).natDegree ≤ S2550F10.natDegree + Qdstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep2 + Ndstep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep2 + Ndstep2).natDegree
        ≤ max (S2550F10 * Qdstep2).natDegree Ndstep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep2, Bdstep2, Qdstep2, Ndstep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep3 : (ZMod 1249)[X] := C 713 + C 1165 * X + C 380 * X ^ 2 + C 942 * X ^ 3 + C 7 * X ^ 4 + C 652 * X ^ 5 + C 234 * X ^ 6 + C 845 * X ^ 7 + C 219 * X ^ 8 + C 411 * X ^ 9
def Bdstep3 : (ZMod 1249)[X] := C 713 + C 1165 * X + C 380 * X ^ 2 + C 942 * X ^ 3 + C 7 * X ^ 4 + C 652 * X ^ 5 + C 234 * X ^ 6 + C 845 * X ^ 7 + C 219 * X ^ 8 + C 411 * X ^ 9
def Qdstep3 : (ZMod 1249)[X] := C 990 + C 1231 * X + C 442 * X ^ 2 + C 576 * X ^ 3 + C 1189 * X ^ 4 + C 1175 * X ^ 5 + C 778 * X ^ 6 + C 602 * X ^ 7 + C 306 * X ^ 8
def Ndstep3 : (ZMod 1249)[X] := C 366 + C 1096 * X + C 1209 * X ^ 2 + C 1248 * X ^ 3 + C 741 * X ^ 4 + C 789 * X ^ 5 + C 164 * X ^ 6 + C 585 * X ^ 7 + C 373 * X ^ 8 + C 126 * X ^ 9
theorem dstep3 : Adstep3 * Bdstep3 = S2550F10 * Qdstep3 + Ndstep3 := by
  have hA : Adstep3.natDegree ≤ 9 := by unfold Adstep3; compute_degree!
  have hB : Bdstep3.natDegree ≤ 9 := by unfold Bdstep3; compute_degree!
  have hQ : Qdstep3.natDegree ≤ 8 := by unfold Qdstep3; compute_degree!
  have hN : Ndstep3.natDegree ≤ 9 := by unfold Ndstep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep3 * Bdstep3).natDegree ≤ 18 := by
    calc (Adstep3 * Bdstep3).natDegree ≤ Adstep3.natDegree + Bdstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep3).natDegree ≤ S2550F10.natDegree + Qdstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep3 + Ndstep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep3 + Ndstep3).natDegree
        ≤ max (S2550F10 * Qdstep3).natDegree Ndstep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep3, Bdstep3, Qdstep3, Ndstep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep4 : (ZMod 1249)[X] := C 366 + C 1096 * X + C 1209 * X ^ 2 + C 1248 * X ^ 3 + C 741 * X ^ 4 + C 789 * X ^ 5 + C 164 * X ^ 6 + C 585 * X ^ 7 + C 373 * X ^ 8 + C 126 * X ^ 9
def Bdstep4 : (ZMod 1249)[X] := C 366 + C 1096 * X + C 1209 * X ^ 2 + C 1248 * X ^ 3 + C 741 * X ^ 4 + C 789 * X ^ 5 + C 164 * X ^ 6 + C 585 * X ^ 7 + C 373 * X ^ 8 + C 126 * X ^ 9
def Qdstep4 : (ZMod 1249)[X] := C 1096 + C 747 * X + C 1013 * X ^ 2 + C 110 * X ^ 3 + C 381 * X ^ 4 + C 1156 * X ^ 5 + C 1028 * X ^ 6 + C 6 * X ^ 7 + C 888 * X ^ 8
def Ndstep4 : (ZMod 1249)[X] := C 374 + C 975 * X + C 97 * X ^ 2 + C 269 * X ^ 3 + C 381 * X ^ 4 + C 788 * X ^ 5 + C 349 * X ^ 6 + C 966 * X ^ 7 + C 1135 * X ^ 8 + C 940 * X ^ 9
theorem dstep4 : Adstep4 * Bdstep4 = S2550F10 * Qdstep4 + Ndstep4 := by
  have hA : Adstep4.natDegree ≤ 9 := by unfold Adstep4; compute_degree!
  have hB : Bdstep4.natDegree ≤ 9 := by unfold Bdstep4; compute_degree!
  have hQ : Qdstep4.natDegree ≤ 8 := by unfold Qdstep4; compute_degree!
  have hN : Ndstep4.natDegree ≤ 9 := by unfold Ndstep4; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep4 * Bdstep4).natDegree ≤ 18 := by
    calc (Adstep4 * Bdstep4).natDegree ≤ Adstep4.natDegree + Bdstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep4).natDegree ≤ S2550F10.natDegree + Qdstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep4 + Ndstep4).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep4 + Ndstep4).natDegree
        ≤ max (S2550F10 * Qdstep4).natDegree Ndstep4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep4, Bdstep4, Qdstep4, Ndstep4, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep5 : (ZMod 1249)[X] := C 374 + C 975 * X + C 97 * X ^ 2 + C 269 * X ^ 3 + C 381 * X ^ 4 + C 788 * X ^ 5 + C 349 * X ^ 6 + C 966 * X ^ 7 + C 1135 * X ^ 8 + C 940 * X ^ 9
def Bdstep5 : (ZMod 1249)[X] := C 374 + C 975 * X + C 97 * X ^ 2 + C 269 * X ^ 3 + C 381 * X ^ 4 + C 788 * X ^ 5 + C 349 * X ^ 6 + C 966 * X ^ 7 + C 1135 * X ^ 8 + C 940 * X ^ 9
def Qdstep5 : (ZMod 1249)[X] := C 277 + C 823 * X + C 388 * X ^ 2 + C 551 * X ^ 3 + C 282 * X ^ 4 + C 148 * X ^ 5 + C 756 * X ^ 6 + C 264 * X ^ 7 + C 557 * X ^ 8
def Ndstep5 : (ZMod 1249)[X] := C 449 + C 1142 * X + C 1059 * X ^ 2 + C 418 * X ^ 3 + C 206 * X ^ 4 + C 302 * X ^ 5 + C 477 * X ^ 6 + C 1019 * X ^ 7 + C 923 * X ^ 8 + C 420 * X ^ 9
theorem dstep5 : Adstep5 * Bdstep5 = S2550F10 * Qdstep5 + Ndstep5 := by
  have hA : Adstep5.natDegree ≤ 9 := by unfold Adstep5; compute_degree!
  have hB : Bdstep5.natDegree ≤ 9 := by unfold Bdstep5; compute_degree!
  have hQ : Qdstep5.natDegree ≤ 8 := by unfold Qdstep5; compute_degree!
  have hN : Ndstep5.natDegree ≤ 9 := by unfold Ndstep5; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep5 * Bdstep5).natDegree ≤ 18 := by
    calc (Adstep5 * Bdstep5).natDegree ≤ Adstep5.natDegree + Bdstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep5).natDegree ≤ S2550F10.natDegree + Qdstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep5 + Ndstep5).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep5 + Ndstep5).natDegree
        ≤ max (S2550F10 * Qdstep5).natDegree Ndstep5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep5, Bdstep5, Qdstep5, Ndstep5, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep6 : (ZMod 1249)[X] := C 449 + C 1142 * X + C 1059 * X ^ 2 + C 418 * X ^ 3 + C 206 * X ^ 4 + C 302 * X ^ 5 + C 477 * X ^ 6 + C 1019 * X ^ 7 + C 923 * X ^ 8 + C 420 * X ^ 9
def Bdstep6 : (ZMod 1249)[X] := C 449 + C 1142 * X + C 1059 * X ^ 2 + C 418 * X ^ 3 + C 206 * X ^ 4 + C 302 * X ^ 5 + C 477 * X ^ 6 + C 1019 * X ^ 7 + C 923 * X ^ 8 + C 420 * X ^ 9
def Qdstep6 : (ZMod 1249)[X] := C 754 + C 1007 * X + C 305 * X ^ 2 + C 128 * X ^ 3 + C 623 * X ^ 4 + C 641 * X ^ 5 + C 437 * X ^ 6 + C 1187 * X ^ 7 + C 291 * X ^ 8
def Ndstep6 : (ZMod 1249)[X] := C 342 + C 295 * X + C 534 * X ^ 2 + C 317 * X ^ 3 + C 1105 * X ^ 4 + C 189 * X ^ 5 + C 891 * X ^ 6 + C 819 * X ^ 7 + C 956 * X ^ 8 + C 667 * X ^ 9
theorem dstep6 : Adstep6 * Bdstep6 = S2550F10 * Qdstep6 + Ndstep6 := by
  have hA : Adstep6.natDegree ≤ 9 := by unfold Adstep6; compute_degree!
  have hB : Bdstep6.natDegree ≤ 9 := by unfold Bdstep6; compute_degree!
  have hQ : Qdstep6.natDegree ≤ 8 := by unfold Qdstep6; compute_degree!
  have hN : Ndstep6.natDegree ≤ 9 := by unfold Ndstep6; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep6 * Bdstep6).natDegree ≤ 18 := by
    calc (Adstep6 * Bdstep6).natDegree ≤ Adstep6.natDegree + Bdstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep6).natDegree ≤ S2550F10.natDegree + Qdstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep6 + Ndstep6).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep6 + Ndstep6).natDegree
        ≤ max (S2550F10 * Qdstep6).natDegree Ndstep6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep6, Bdstep6, Qdstep6, Ndstep6, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep7 : (ZMod 1249)[X] := C 342 + C 295 * X + C 534 * X ^ 2 + C 317 * X ^ 3 + C 1105 * X ^ 4 + C 189 * X ^ 5 + C 891 * X ^ 6 + C 819 * X ^ 7 + C 956 * X ^ 8 + C 667 * X ^ 9
def Bdstep7 : (ZMod 1249)[X] := C 342 + C 295 * X + C 534 * X ^ 2 + C 317 * X ^ 3 + C 1105 * X ^ 4 + C 189 * X ^ 5 + C 891 * X ^ 6 + C 819 * X ^ 7 + C 956 * X ^ 8 + C 667 * X ^ 9
def Qdstep7 : (ZMod 1249)[X] := C 2 + C 694 * X + C 522 * X ^ 2 + C 389 * X ^ 3 + C 429 * X ^ 4 + C 172 * X ^ 5 + C 460 * X ^ 6 + C 313 * X ^ 7 + C 245 * X ^ 8
def Ndstep7 : (ZMod 1249)[X] := C 896 + C 17 * X + C 668 * X ^ 2 + C 660 * X ^ 3 + C 472 * X ^ 4 + C 352 * X ^ 5 + C 863 * X ^ 6 + C 404 * X ^ 7 + C 356 * X ^ 8 + C 1075 * X ^ 9
theorem dstep7 : Adstep7 * Bdstep7 = S2550F10 * Qdstep7 + Ndstep7 := by
  have hA : Adstep7.natDegree ≤ 9 := by unfold Adstep7; compute_degree!
  have hB : Bdstep7.natDegree ≤ 9 := by unfold Bdstep7; compute_degree!
  have hQ : Qdstep7.natDegree ≤ 8 := by unfold Qdstep7; compute_degree!
  have hN : Ndstep7.natDegree ≤ 9 := by unfold Ndstep7; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep7 * Bdstep7).natDegree ≤ 18 := by
    calc (Adstep7 * Bdstep7).natDegree ≤ Adstep7.natDegree + Bdstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep7).natDegree ≤ S2550F10.natDegree + Qdstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep7 + Ndstep7).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep7 + Ndstep7).natDegree
        ≤ max (S2550F10 * Qdstep7).natDegree Ndstep7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep7, Bdstep7, Qdstep7, Ndstep7, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep8 : (ZMod 1249)[X] := C 896 + C 17 * X + C 668 * X ^ 2 + C 660 * X ^ 3 + C 472 * X ^ 4 + C 352 * X ^ 5 + C 863 * X ^ 6 + C 404 * X ^ 7 + C 356 * X ^ 8 + C 1075 * X ^ 9
def Bdstep8 : (ZMod 1249)[X] := C 896 + C 17 * X + C 668 * X ^ 2 + C 660 * X ^ 3 + C 472 * X ^ 4 + C 352 * X ^ 5 + C 863 * X ^ 6 + C 404 * X ^ 7 + C 356 * X ^ 8 + C 1075 * X ^ 9
def Qdstep8 : (ZMod 1249)[X] := C 290 + C 182 * X + C 10 * X ^ 2 + C 436 * X ^ 3 + C 984 * X ^ 4 + C 44 * X ^ 5 + C 323 * X ^ 6 + C 1125 * X ^ 7 + C 300 * X ^ 8
def Ndstep8 : (ZMod 1249)[X] := C 124 + C 415 * X + C 501 * X ^ 2 + C 562 * X ^ 3 + C 686 * X ^ 4 + C 348 * X ^ 5 + C 1108 * X ^ 6 + C 428 * X ^ 7 + C 537 * X ^ 8 + C 111 * X ^ 9
theorem dstep8 : Adstep8 * Bdstep8 = S2550F10 * Qdstep8 + Ndstep8 := by
  have hA : Adstep8.natDegree ≤ 9 := by unfold Adstep8; compute_degree!
  have hB : Bdstep8.natDegree ≤ 9 := by unfold Bdstep8; compute_degree!
  have hQ : Qdstep8.natDegree ≤ 8 := by unfold Qdstep8; compute_degree!
  have hN : Ndstep8.natDegree ≤ 9 := by unfold Ndstep8; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep8 * Bdstep8).natDegree ≤ 18 := by
    calc (Adstep8 * Bdstep8).natDegree ≤ Adstep8.natDegree + Bdstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep8).natDegree ≤ S2550F10.natDegree + Qdstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep8 + Ndstep8).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep8 + Ndstep8).natDegree
        ≤ max (S2550F10 * Qdstep8).natDegree Ndstep8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep8, Bdstep8, Qdstep8, Ndstep8, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Adstep9 : (ZMod 1249)[X] := C 124 + C 415 * X + C 501 * X ^ 2 + C 562 * X ^ 3 + C 686 * X ^ 4 + C 348 * X ^ 5 + C 1108 * X ^ 6 + C 428 * X ^ 7 + C 537 * X ^ 8 + C 111 * X ^ 9
def Bdstep9 : (ZMod 1249)[X] := C 124 + C 415 * X + C 501 * X ^ 2 + C 562 * X ^ 3 + C 686 * X ^ 4 + C 348 * X ^ 5 + C 1108 * X ^ 6 + C 428 * X ^ 7 + C 537 * X ^ 8 + C 111 * X ^ 9
def Qdstep9 : (ZMod 1249)[X] := C 1000 + C 1213 * X + C 757 * X ^ 2 + C 114 * X ^ 3 + C 805 * X ^ 4 + C 793 * X ^ 5 + C 928 * X ^ 6 + C 716 * X ^ 7 + C 1080 * X ^ 8
def Ndstep9 : (ZMod 1249)[X] := C 1173 + C 266 * X + C 309 * X ^ 2 + C 1199 * X ^ 3 + C 260 * X ^ 4 + C 457 * X ^ 5 + C 906 * X ^ 6 + C 116 * X ^ 7 + C 548 * X ^ 8 + C 571 * X ^ 9
theorem dstep9 : Adstep9 * Bdstep9 = S2550F10 * Qdstep9 + Ndstep9 := by
  have hA : Adstep9.natDegree ≤ 9 := by unfold Adstep9; compute_degree!
  have hB : Bdstep9.natDegree ≤ 9 := by unfold Bdstep9; compute_degree!
  have hQ : Qdstep9.natDegree ≤ 8 := by unfold Qdstep9; compute_degree!
  have hN : Ndstep9.natDegree ≤ 9 := by unfold Ndstep9; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Adstep9 * Bdstep9).natDegree ≤ 18 := by
    calc (Adstep9 * Bdstep9).natDegree ≤ Adstep9.natDegree + Bdstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qdstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep9).natDegree ≤ S2550F10.natDegree + Qdstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qdstep9 + Ndstep9).natDegree ≤ 18 := by
    calc (S2550F10 * Qdstep9 + Ndstep9).natDegree
        ≤ max (S2550F10 * Qdstep9).natDegree Ndstep9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Adstep9, Bdstep9, Qdstep9, Ndstep9, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def E0 : (ZMod 1249)[X] := C 1173 + C 266 * X + C 309 * X ^ 2 + C 1199 * X ^ 3 + C 260 * X ^ 4 + C 457 * X ^ 5 + C 906 * X ^ 6 + C 116 * X ^ 7 + C 548 * X ^ 8 + C 571 * X ^ 9
def E1 : (ZMod 1249)[X] := C 1232 + C 233 * X + C 46 * X ^ 2 + C 766 * X ^ 3 + C 460 * X ^ 4 + C 118 * X ^ 5 + C 1175 * X ^ 6 + C 1002 * X ^ 7 + C 202 * X ^ 8 + C 723 * X ^ 9
def E2 : (ZMod 1249)[X] := C 188 + C 283 * X + C 412 * X ^ 2 + C 79 * X ^ 3 + C 561 * X ^ 4 + C 808 * X ^ 5 + C 677 * X ^ 6 + C 698 * X ^ 7 + C 975 * X ^ 8 + C 202 * X ^ 9
def E3 : (ZMod 1249)[X] := C 1165 + C 317 * X + C 1042 * X ^ 2 + C 593 * X ^ 3 + C 1167 * X ^ 4 + C 1164 * X ^ 5 + C 313 * X ^ 6 + C 970 * X ^ 7 + C 89 * X ^ 8 + C 1069 * X ^ 9
def E4 : (ZMod 1249)[X] := C 1194 + C 810 * X + C 856 * X ^ 2 + C 203 * X ^ 3 + C 881 * X ^ 4 + C 314 * X ^ 5 + C 738 * X ^ 6 + C 1237 * X ^ 7 + C 176 * X ^ 8 + C 1189 * X ^ 9
def Aestep0 : (ZMod 1249)[X] := C 1173 + C 266 * X + C 309 * X ^ 2 + C 1199 * X ^ 3 + C 260 * X ^ 4 + C 457 * X ^ 5 + C 906 * X ^ 6 + C 116 * X ^ 7 + C 548 * X ^ 8 + C 571 * X ^ 9
def Bestep0 : (ZMod 1249)[X] := C 342 + C 295 * X + C 534 * X ^ 2 + C 317 * X ^ 3 + C 1105 * X ^ 4 + C 189 * X ^ 5 + C 891 * X ^ 6 + C 819 * X ^ 7 + C 956 * X ^ 8 + C 667 * X ^ 9
def Qestep0 : (ZMod 1249)[X] := C 289 + C 455 * X + C 1193 * X ^ 2 + C 303 * X ^ 3 + C 209 * X ^ 4 + C 567 * X ^ 5 + C 759 * X ^ 6 + C 1071 * X ^ 7 + C 1161 * X ^ 8
def Nestep0 : (ZMod 1249)[X] := C 1232 + C 233 * X + C 46 * X ^ 2 + C 766 * X ^ 3 + C 460 * X ^ 4 + C 118 * X ^ 5 + C 1175 * X ^ 6 + C 1002 * X ^ 7 + C 202 * X ^ 8 + C 723 * X ^ 9
theorem estep0 : Aestep0 * Bestep0 = S2550F10 * Qestep0 + Nestep0 := by
  have hA : Aestep0.natDegree ≤ 9 := by unfold Aestep0; compute_degree!
  have hB : Bestep0.natDegree ≤ 9 := by unfold Bestep0; compute_degree!
  have hQ : Qestep0.natDegree ≤ 8 := by unfold Qestep0; compute_degree!
  have hN : Nestep0.natDegree ≤ 9 := by unfold Nestep0; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aestep0 * Bestep0).natDegree ≤ 18 := by
    calc (Aestep0 * Bestep0).natDegree ≤ Aestep0.natDegree + Bestep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qestep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep0).natDegree ≤ S2550F10.natDegree + Qestep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qestep0 + Nestep0).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep0 + Nestep0).natDegree
        ≤ max (S2550F10 * Qestep0).natDegree Nestep0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aestep0, Bestep0, Qestep0, Nestep0, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Aestep1 : (ZMod 1249)[X] := C 1232 + C 233 * X + C 46 * X ^ 2 + C 766 * X ^ 3 + C 460 * X ^ 4 + C 118 * X ^ 5 + C 1175 * X ^ 6 + C 1002 * X ^ 7 + C 202 * X ^ 8 + C 723 * X ^ 9
def Bestep1 : (ZMod 1249)[X] := C 449 + C 1142 * X + C 1059 * X ^ 2 + C 418 * X ^ 3 + C 206 * X ^ 4 + C 302 * X ^ 5 + C 477 * X ^ 6 + C 1019 * X ^ 7 + C 923 * X ^ 8 + C 420 * X ^ 9
def Qestep1 : (ZMod 1249)[X] := C 695 + C 572 * X + C 59 * X ^ 2 + C 277 * X ^ 3 + C 842 * X ^ 4 + C 457 * X ^ 5 + C 1153 * X ^ 6 + C 491 * X ^ 7 + C 153 * X ^ 8
def Nestep1 : (ZMod 1249)[X] := C 188 + C 283 * X + C 412 * X ^ 2 + C 79 * X ^ 3 + C 561 * X ^ 4 + C 808 * X ^ 5 + C 677 * X ^ 6 + C 698 * X ^ 7 + C 975 * X ^ 8 + C 202 * X ^ 9
theorem estep1 : Aestep1 * Bestep1 = S2550F10 * Qestep1 + Nestep1 := by
  have hA : Aestep1.natDegree ≤ 9 := by unfold Aestep1; compute_degree!
  have hB : Bestep1.natDegree ≤ 9 := by unfold Bestep1; compute_degree!
  have hQ : Qestep1.natDegree ≤ 8 := by unfold Qestep1; compute_degree!
  have hN : Nestep1.natDegree ≤ 9 := by unfold Nestep1; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aestep1 * Bestep1).natDegree ≤ 18 := by
    calc (Aestep1 * Bestep1).natDegree ≤ Aestep1.natDegree + Bestep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qestep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep1).natDegree ≤ S2550F10.natDegree + Qestep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qestep1 + Nestep1).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep1 + Nestep1).natDegree
        ≤ max (S2550F10 * Qestep1).natDegree Nestep1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aestep1, Bestep1, Qestep1, Nestep1, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Aestep2 : (ZMod 1249)[X] := C 188 + C 283 * X + C 412 * X ^ 2 + C 79 * X ^ 3 + C 561 * X ^ 4 + C 808 * X ^ 5 + C 677 * X ^ 6 + C 698 * X ^ 7 + C 975 * X ^ 8 + C 202 * X ^ 9
def Bestep2 : (ZMod 1249)[X] := C 374 + C 975 * X + C 97 * X ^ 2 + C 269 * X ^ 3 + C 381 * X ^ 4 + C 788 * X ^ 5 + C 349 * X ^ 6 + C 966 * X ^ 7 + C 1135 * X ^ 8 + C 940 * X ^ 9
def Qestep2 : (ZMod 1249)[X] := C 888 + C 948 * X + C 481 * X ^ 2 + C 383 * X ^ 3 + C 350 * X ^ 4 + C 93 * X ^ 5 + C 364 * X ^ 6 + C 932 * X ^ 7 + C 32 * X ^ 8
def Nestep2 : (ZMod 1249)[X] := C 1165 + C 317 * X + C 1042 * X ^ 2 + C 593 * X ^ 3 + C 1167 * X ^ 4 + C 1164 * X ^ 5 + C 313 * X ^ 6 + C 970 * X ^ 7 + C 89 * X ^ 8 + C 1069 * X ^ 9
theorem estep2 : Aestep2 * Bestep2 = S2550F10 * Qestep2 + Nestep2 := by
  have hA : Aestep2.natDegree ≤ 9 := by unfold Aestep2; compute_degree!
  have hB : Bestep2.natDegree ≤ 9 := by unfold Bestep2; compute_degree!
  have hQ : Qestep2.natDegree ≤ 8 := by unfold Qestep2; compute_degree!
  have hN : Nestep2.natDegree ≤ 9 := by unfold Nestep2; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aestep2 * Bestep2).natDegree ≤ 18 := by
    calc (Aestep2 * Bestep2).natDegree ≤ Aestep2.natDegree + Bestep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qestep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep2).natDegree ≤ S2550F10.natDegree + Qestep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qestep2 + Nestep2).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep2 + Nestep2).natDegree
        ≤ max (S2550F10 * Qestep2).natDegree Nestep2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aestep2, Bestep2, Qestep2, Nestep2, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

def Aestep3 : (ZMod 1249)[X] := C 1165 + C 317 * X + C 1042 * X ^ 2 + C 593 * X ^ 3 + C 1167 * X ^ 4 + C 1164 * X ^ 5 + C 313 * X ^ 6 + C 970 * X ^ 7 + C 89 * X ^ 8 + C 1069 * X ^ 9
def Bestep3 : (ZMod 1249)[X] := C 762 + C 335 * X + C 659 * X ^ 2 + C 508 * X ^ 3 + C 66 * X ^ 4 + C 796 * X ^ 5 + C 770 * X ^ 6 + C 670 * X ^ 7 + C 293 * X ^ 8 + C 881 * X ^ 9
def Qestep3 : (ZMod 1249)[X] := C 960 + C 1091 * X + C 711 * X ^ 2 + C 285 * X ^ 3 + C 578 * X ^ 4 + C 253 * X ^ 5 + C 587 * X ^ 6 + C 1159 * X ^ 7 + C 43 * X ^ 8
def Nestep3 : (ZMod 1249)[X] := C 1194 + C 810 * X + C 856 * X ^ 2 + C 203 * X ^ 3 + C 881 * X ^ 4 + C 314 * X ^ 5 + C 738 * X ^ 6 + C 1237 * X ^ 7 + C 176 * X ^ 8 + C 1189 * X ^ 9
theorem estep3 : Aestep3 * Bestep3 = S2550F10 * Qestep3 + Nestep3 := by
  have hA : Aestep3.natDegree ≤ 9 := by unfold Aestep3; compute_degree!
  have hB : Bestep3.natDegree ≤ 9 := by unfold Bestep3; compute_degree!
  have hQ : Qestep3.natDegree ≤ 8 := by unfold Qestep3; compute_degree!
  have hN : Nestep3.natDegree ≤ 9 := by unfold Nestep3; compute_degree!
  have hF : S2550F10.natDegree = 10 := by unfold S2550F10; compute_degree!
  have hL : (Aestep3 * Bestep3).natDegree ≤ 18 := by
    calc (Aestep3 * Bestep3).natDegree ≤ Aestep3.natDegree + Bestep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (S2550F10 * Qestep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep3).natDegree ≤ S2550F10.natDegree + Qestep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (S2550F10 * Qestep3 + Nestep3).natDegree ≤ 18 := by
    calc (S2550F10 * Qestep3 + Nestep3).natDegree
        ≤ max (S2550F10 * Qestep3).natDegree Nestep3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [Aestep3, Bestep3, Qestep3, Nestep3, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

end