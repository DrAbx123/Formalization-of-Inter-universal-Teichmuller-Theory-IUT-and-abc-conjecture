import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

/-! # S2589ProductDAlt: independent Product D certificate -/

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2589ProductDAltActual

abbrev F10 : (ZMod 1249)[X] := S2550F10

def sC : (ZMod 1249)[X] :=
  C 638 + C 237 * X + C 462 * X^2 + C 445 * X^3 + C 530 * X^4 +
  C 386 * X^5 + C 1217 * X^6 + C 766 * X^7 + C 682 * X^8 + C 825 * X^9

def sD : (ZMod 1249)[X] :=
  C 1116 + C 1078 * X + C 786 * X^2 + C 643 * X^3 + C 776 * X^4 +
  C 720 * X^5 + C 1083 * X^6 + C 988 * X^7 + C 1201 * X^8 + C 56 * X^9

theorem prodD : sC * S2560Batch1CorrectActual.R0 = F10 * C 825 + sD := by
  have hA : sC.natDegree ≤ 9 := by unfold sC; compute_degree!
  have hB : S2560Batch1CorrectActual.R0.natDegree ≤ 1 := by unfold S2560Batch1CorrectActual.R0; compute_degree!
  have hR : sD.natDegree ≤ 9 := by unfold sD; compute_degree!
  have hL : (sC * S2560Batch1CorrectActual.R0).natDegree ≤ 10 := by
    calc _ ≤ sC.natDegree + S2560Batch1CorrectActual.R0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 10 := by omega
  have h1 : (F10 * C 825).natDegree ≤ 10 := by
    calc _ ≤ F10.natDegree + (C 825 : (ZMod 1249)[X]).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 10 := by
        have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
        have hc : (C 825 : (ZMod 1249)[X]).natDegree ≤ 0 := by compute_degree!
        omega
  have hR2 : (F10 * C 825 + sD).natDegree ≤ 10 := by
    calc _ ≤ max (F10 * C 825).natDegree sD.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 10 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      (simp [sC, sD, S2560Batch1CorrectActual.R0, F10, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
        Polynomial.coeff_X_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

#print axioms prodD

end LeanFormal.IUT.XiFPaper.S2589ProductDAltActual
end
