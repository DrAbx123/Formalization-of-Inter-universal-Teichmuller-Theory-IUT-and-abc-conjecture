import tmp.sheaf.xif.paper.S2560Batch1CorrectActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
namespace LeanFormal.IUT.XiFPaper.S2586ProductAActual
abbrev F10 : (ZMod 1249)[X] := S2550F10
def q0 : (ZMod 1249)[X] := C 1147 + C 74 * X + C 32 * X ^ 2 + C 817 * X ^ 3 + C 400 * X ^ 4 + C 1065 * X ^ 5 + C 203 * X ^ 6 + C 651 * X ^ 7 + C 1043 * X ^ 8
def r0 : (ZMod 1249)[X] := C 428 + C 197 * X + C 164 * X ^ 2 + C 226 * X ^ 3 + C 199 * X ^ 4 + C 1137 * X ^ 5 + C 1163 * X ^ 6 + C 780 * X ^ 7 + C 1163 * X ^ 8 + C 617 * X ^ 9
lemma prodA : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 = F10 * q0 + r0 := by
  have hL : (LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7).natDegree ≤ 18 := by
    calc _ ≤ LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10.natDegree + LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by
        have h1 : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10; compute_degree!
        have h2 : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7; compute_degree!
        omega
  have hR : (F10 * q0 + r0).natDegree ≤ 18 := by
    have h1 : (F10 * q0).natDegree ≤ 18 := by
      calc _ ≤ F10.natDegree + q0.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 18 := by
          have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
          have hq : q0.natDegree ≤ 8 := by unfold q0; compute_degree!
          omega
    have h2 : r0.natDegree ≤ 9 := by unfold r0; compute_degree!
    calc (F10 * q0 + r0).natDegree ≤ max (F10 * q0).natDegree r0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10, LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7, q0, r0, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
#print axioms prodA
end LeanFormal.IUT.XiFPaper.S2586ProductAActual
end
