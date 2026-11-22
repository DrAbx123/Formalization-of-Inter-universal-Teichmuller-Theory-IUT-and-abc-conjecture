import tmp.sheaf.xif.paper.S2587ProductBAltActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2586ProductAActual
open LeanFormal.IUT.XiFPaper.S2587ProductBAltActual
namespace LeanFormal.IUT.XiFPaper.S2588ProductCDActualAdapted
abbrev F10 : (ZMod 1249)[X] := S2550F10
def qC : (ZMod 1249)[X] := C 513 + C 383 * X + C 460 * X ^ 2 + C 820 * X ^ 3 + C 108 * X ^ 4 + C 945 * X ^ 5 + C 1018 * X ^ 6 + C 830 * X ^ 7 + C 1099 * X ^ 8
def rC : (ZMod 1249)[X] := C 638 + C 237 * X + C 462 * X ^ 2 + C 445 * X ^ 3 + C 530 * X ^ 4 + C 386 * X ^ 5 + C 1217 * X ^ 6 + C 766 * X ^ 7 + C 682 * X ^ 8 + C 825 * X ^ 9
def qD : (ZMod 1249)[X] := C 825
def rD : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
lemma prodC : rB * R5 = F10 * qC + rC := by
  have hA : rB.natDegree ≤ 9 := by unfold rB S2587ProductBAltActual.rB; compute_degree!
  have hB : R5.natDegree ≤ 9 := by unfold R5; compute_degree!
  have hQ : qC.natDegree ≤ 8 := by unfold qC; compute_degree!
  have hR : rC.natDegree ≤ 9 := by unfold rC; compute_degree!
  have hL : (rB * R5).natDegree ≤ 18 := by
    calc _ ≤ rB.natDegree + R5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * qC).natDegree ≤ 18 := by
    calc _ ≤ F10.natDegree + qC.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by
        have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
        omega
  have hRn : (F10 * qC + rC).natDegree ≤ 18 := by
    calc _ ≤ max (F10 * qC).natDegree rC.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [rB, S2587ProductBAltActual.rB, R5, qC, rC, F10, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow,
        Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma prodD : rC * R0 = F10 * qD + rD := by
  have hA : rC.natDegree ≤ 9 := by unfold rC; compute_degree!
  have hB : R0.natDegree ≤ 9 := by unfold R0; compute_degree!
  have hQ : qD.natDegree ≤ 8 := by unfold qD; compute_degree!
  have hR : rD.natDegree ≤ 9 := by unfold rD; compute_degree!
  have hL : (rC * R0).natDegree ≤ 18 := by
    calc _ ≤ rC.natDegree + R0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * qD).natDegree ≤ 18 := by
    calc _ ≤ F10.natDegree + qD.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by
        have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
        omega
  have hRn : (F10 * qD + rD).natDegree ≤ 18 := by
    calc _ ≤ max (F10 * qD).natDegree rD.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [rC, R0, qD, rD, F10, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow,
        Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma chain1249_Rprod :
    R10 * R7 * R6 * R5 * R0 =
      F10 * (q0 * R6 * R5 * R0 + qB * R5 * R0 + qC * R0 + qD) + rD := by
  calc
    R10 * R7 * R6 * R5 * R0 = (F10 * q0 + r0) * R6 * R5 * R0 := by rw [prodA]
    _ = F10 * (q0 * R6 * R5 * R0) + r0 * R6 * R5 * R0 := by ring
    _ = F10 * (q0 * R6 * R5 * R0) + (F10 * qB + rB) * R5 * R0 := by rw [prodB]
    _ = F10 * (q0 * R6 * R5 * R0 + qB * R5 * R0) + rB * R5 * R0 := by ring
    _ = F10 * (q0 * R6 * R5 * R0 + qB * R5 * R0) + (F10 * qC + rC) * R0 := by rw [prodC]
    _ = F10 * (q0 * R6 * R5 * R0 + qB * R5 * R0 + qC * R0) + rC * R0 := by ring
    _ = F10 * (q0 * R6 * R5 * R0 + qB * R5 * R0 + qC * R0) + (F10 * qD + rD) := by rw [prodD]
    _ = F10 * (q0 * R6 * R5 * R0 + qB * R5 * R0 + qC * R0 + qD) + rD := by ring
#check prodC
#check prodD
#check chain1249_Rprod
end LeanFormal.IUT.XiFPaper.S2588ProductCDActualAdapted
end
