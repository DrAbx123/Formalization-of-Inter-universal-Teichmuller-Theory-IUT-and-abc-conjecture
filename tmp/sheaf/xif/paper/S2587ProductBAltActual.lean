import tmp.sheaf.xif.paper.S2586ProductAActual

/-! # S2587ProductBAlt: independent Product B certificate -/

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2586ProductAActual

namespace LeanFormal.IUT.XiFPaper.S2587ProductBAltActual

abbrev F10 : (ZMod 1249)[X] := S2550F10

def qB : (ZMod 1249)[X] :=
  C 362 + C 564 * X + C 581 * X^2 + C 111 * X^3 + C 845 * X^4 +
  C 167 * X^5 + C 1113 * X^6 + C 1173 * X^7 + C 1208 * X^8

def rB : (ZMod 1249)[X] :=
  C 656 + C 538 * X + C 1242 * X^2 + C 988 * X^3 + C 45 * X^4 +
  C 358 * X^5 + C 395 * X^6 + C 241 * X^7 + C 245 * X^8 + C 280 * X^9

theorem prodB : r0 * S2560Batch1CorrectActual.R6 = F10 * qB + rB := by
  have hA : r0.natDegree ≤ 9 := by unfold r0; compute_degree!
  have hB : S2560Batch1CorrectActual.R6.natDegree ≤ 9 := by unfold S2560Batch1CorrectActual.R6; compute_degree!
  have hQ : qB.natDegree ≤ 8 := by unfold qB; compute_degree!
  have hR : rB.natDegree ≤ 9 := by unfold rB; compute_degree!
  have hL : (r0 * S2560Batch1CorrectActual.R6).natDegree ≤ 18 := by
    calc _ ≤ r0.natDegree + S2560Batch1CorrectActual.R6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * qB).natDegree ≤ 18 := by
    calc _ ≤ F10.natDegree + qB.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by
        have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
        omega
  have hR2 : (F10 * qB + rB).natDegree ≤ 18 := by
    calc _ ≤ max (F10 * qB).natDegree rB.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [r0, S2560Batch1CorrectActual.R6, qB, rB, F10, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
        Polynomial.coeff_X_pow, Polynomial.coeff_one,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem prodB_chain : S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 = F10 * (q0 * S2560Batch1CorrectActual.R6 + qB) + rB := by
  calc
    S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 = (F10 * q0 + r0) * S2560Batch1CorrectActual.R6 := by rw [prodA]
    _ = F10 * (q0 * S2560Batch1CorrectActual.R6) + r0 * S2560Batch1CorrectActual.R6 := by ring
    _ = F10 * (q0 * S2560Batch1CorrectActual.R6) + (F10 * qB + rB) := by rw [prodB]
    _ = F10 * (q0 * S2560Batch1CorrectActual.R6 + qB) + rB := by ring

#print axioms prodB
#print axioms prodB_chain

end LeanFormal.IUT.XiFPaper.S2587ProductBAltActual
end
