import tmp.sheaf.xif.paper.S2560Batch1CorrectActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
namespace LeanFormal.IUT.XiFPaper.S2589ProductDActual
abbrev F10 : (ZMod 1249)[X] := S2550F10
def sC : (ZMod 1249)[X] := C 638 + C 237 * X + C 462 * X ^ 2 + C 445 * X ^ 3 + C 530 * X ^ 4 + C 386 * X ^ 5 + C 1217 * X ^ 6 + C 766 * X ^ 7 + C 682 * X ^ 8 + C 825 * X ^ 9
def qD : (ZMod 1249)[X] := C 825
def rD : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
lemma prodD : sC * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 = F10 * qD + rD := by
  have hA : sC.natDegree ≤ 9 := by unfold sC; compute_degree!
  have hB : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0; compute_degree!
  have hQ : qD.natDegree ≤ 8 := by unfold qD; compute_degree!
  have hR : rD.natDegree ≤ 9 := by unfold rD; compute_degree!
  have hL : (sC * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0).natDegree ≤ 18 := by
    calc _ ≤ sC.natDegree + LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * qD).natDegree ≤ 18 := by
    calc _ ≤ F10.natDegree + qD.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by
        have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
        omega
  have hRn : (F10 * qD + rD).natDegree ≤ 18 := by
    calc _ ≤ max (F10 * qD).natDegree rD.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [sC, LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0, qD, rD, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
#print axioms prodD
end LeanFormal.IUT.XiFPaper.S2589ProductDActual
end
