import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

/-! # S2588ProductCAlt: independent Product C certificate -/

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2588ProductCAltActual

abbrev F10 : (ZMod 1249)[X] := S2550F10

def sB : (ZMod 1249)[X] :=
  C 656 + C 538 * X + C 1242 * X^2 + C 988 * X^3 + C 45 * X^4 +
  C 358 * X^5 + C 395 * X^6 + C 241 * X^7 + C 245 * X^8 + C 280 * X^9

def qC : (ZMod 1249)[X] :=
  C 513 + C 383 * X + C 460 * X^2 + C 820 * X^3 + C 108 * X^4 +
  C 945 * X^5 + C 1018 * X^6 + C 830 * X^7 + C 1099 * X^8

def sC : (ZMod 1249)[X] :=
  C 638 + C 237 * X + C 462 * X^2 + C 445 * X^3 + C 530 * X^4 +
  C 386 * X^5 + C 1217 * X^6 + C 766 * X^7 + C 682 * X^8 + C 825 * X^9

theorem prodC : sB * S2560Batch1CorrectActual.R5 = F10 * qC + sC := by
  have hA : sB.natDegree ≤ 9 := by unfold sB; compute_degree!
  have hB : S2560Batch1CorrectActual.R5.natDegree ≤ 9 := by unfold S2560Batch1CorrectActual.R5; compute_degree!
  have hQ : qC.natDegree ≤ 8 := by unfold qC; compute_degree!
  have hR : sC.natDegree ≤ 9 := by unfold sC; compute_degree!
  have hL : (sB * S2560Batch1CorrectActual.R5).natDegree ≤ 18 := by
    calc _ ≤ sB.natDegree + S2560Batch1CorrectActual.R5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * qC).natDegree ≤ 18 := by
    calc _ ≤ F10.natDegree + qC.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by
        have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
        omega
  have hR2 : (F10 * qC + sC).natDegree ≤ 18 := by
    calc _ ≤ max (F10 * qC).natDegree sC.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [sB, S2560Batch1CorrectActual.R5, qC, sC, F10, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
        Polynomial.coeff_X_pow, Polynomial.coeff_one,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

#print axioms prodC

end LeanFormal.IUT.XiFPaper.S2588ProductCAltActual
end
