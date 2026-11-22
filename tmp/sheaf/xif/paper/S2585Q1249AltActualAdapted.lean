import tmp.sheaf.xif.paper.S2560Batch1CorrectActual
import tmp.sheaf.xif.paper.S2582PowerTwoChainAltActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
namespace LeanFormal.IUT.XiFPaper.S2585Q1249AltActualAdapted
abbrev F10 : (ZMod 1249)[X] := S2550F10
def q0 : (ZMod 1249)[X] := C 1147 + C 74 * X + C 32 * X ^ 2 + C 817 * X ^ 3 + C 400 * X ^ 4 + C 1065 * X ^ 5 + C 203 * X ^ 6 + C 651 * X ^ 7 + C 1043 * X ^ 8
def r0 : (ZMod 1249)[X] := C 428 + C 197 * X + C 164 * X ^ 2 + C 226 * X ^ 3 + C 199 * X ^ 4 + C 1137 * X ^ 5 + C 1163 * X ^ 6 + C 780 * X ^ 7 + C 1163 * X ^ 8 + C 617 * X ^ 9
def q1 : (ZMod 1249)[X] := C 362 + C 564 * X + C 581 * X ^ 2 + C 111 * X ^ 3 + C 845 * X ^ 4 + C 167 * X ^ 5 + C 1113 * X ^ 6 + C 1173 * X ^ 7 + C 1208 * X ^ 8
def r1 : (ZMod 1249)[X] := C 656 + C 538 * X + C 1242 * X ^ 2 + C 988 * X ^ 3 + C 45 * X ^ 4 + C 358 * X ^ 5 + C 395 * X ^ 6 + C 241 * X ^ 7 + C 245 * X ^ 8 + C 280 * X ^ 9
def q2 : (ZMod 1249)[X] := C 513 + C 383 * X + C 460 * X ^ 2 + C 820 * X ^ 3 + C 108 * X ^ 4 + C 945 * X ^ 5 + C 1018 * X ^ 6 + C 830 * X ^ 7 + C 1099 * X ^ 8
def r2 : (ZMod 1249)[X] := C 638 + C 237 * X + C 462 * X ^ 2 + C 445 * X ^ 3 + C 530 * X ^ 4 + C 386 * X ^ 5 + C 1217 * X ^ 6 + C 766 * X ^ 7 + C 682 * X ^ 8 + C 825 * X ^ 9
def q3 : (ZMod 1249)[X] := C 825
def r3 : (ZMod 1249)[X] := C 1116 + C 1078 * X + C 786 * X ^ 2 + C 643 * X ^ 3 + C 776 * X ^ 4 + C 720 * X ^ 5 + C 1083 * X ^ 6 + C 988 * X ^ 7 + C 1201 * X ^ 8 + C 56 * X ^ 9
lemma helper1 {P R S T Q : (ZMod 1249)[X]} (h : F10 ∣ P - R) (hprod : R * S = F10 * Q + T) : F10 ∣ P * S - T := by
  obtain ⟨A, hA⟩ := h
  have hPS : P * S - T = (P - R) * S + (R * S - T) := by ring
  rw [hPS]
  apply dvd_add
  · exact dvd_mul_of_dvd_left ⟨A, hA⟩ S
  · refine ⟨Q, ?_⟩
    rw [hprod]
    ring
lemma helper2 {P Q P' Q' : (ZMod 1249)[X]} (hP : F10 ∣ P - P') (hQ : F10 ∣ Q - Q') : F10 ∣ P * Q - P' * Q' := by
  have h : P * Q - P' * Q' = (P - P') * Q + P' * (Q - Q') := by ring
  rw [h]
  apply dvd_add
  · exact dvd_mul_of_dvd_left hP Q
  · exact dvd_mul_of_dvd_left (by simpa [mul_comm] using hQ) P'
lemma prod0 : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 = F10 * q0 + r0 := by
  have hA : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10; compute_degree!
  have hB : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7; compute_degree!
  have hQ : q0.natDegree ≤ 8 := by unfold q0; compute_degree!
  have hR : r0.natDegree ≤ 9 := by unfold r0; compute_degree!
  have hL : (LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7).natDegree ≤ 18 := by
    calc (LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7).natDegree ≤ LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10.natDegree + LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * q0).natDegree ≤ 18 := by
    calc (F10 * q0).natDegree ≤ F10.natDegree + q0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hRn : (F10 * q0 + r0).natDegree ≤ 18 := by
    calc (F10 * q0 + r0).natDegree ≤ max (F10 * q0).natDegree r0.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10, LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7, q0, r0, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
lemma prod1 : r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 = F10 * q1 + r1 := by
  have hA : r0.natDegree ≤ 9 := by unfold r0; compute_degree!
  have hB : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6; compute_degree!
  have hQ : q1.natDegree ≤ 8 := by unfold q1; compute_degree!
  have hR : r1.natDegree ≤ 9 := by unfold r1; compute_degree!
  have hL : (r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6).natDegree ≤ 18 := by
    calc (r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6).natDegree ≤ r0.natDegree + LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * q1).natDegree ≤ 18 := by
    calc (F10 * q1).natDegree ≤ F10.natDegree + q1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hRn : (F10 * q1 + r1).natDegree ≤ 18 := by
    calc (F10 * q1 + r1).natDegree ≤ max (F10 * q1).natDegree r1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [r0, LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6, q1, r1, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
lemma prod2 : r1 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 = F10 * q2 + r2 := by
  have hA : r1.natDegree ≤ 9 := by unfold r1; compute_degree!
  have hB : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5; compute_degree!
  have hQ : q2.natDegree ≤ 8 := by unfold q2; compute_degree!
  have hR : r2.natDegree ≤ 9 := by unfold r2; compute_degree!
  have hL : (r1 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5).natDegree ≤ 18 := by
    calc (r1 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5).natDegree ≤ r1.natDegree + LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * q2).natDegree ≤ 18 := by
    calc (F10 * q2).natDegree ≤ F10.natDegree + q2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hRn : (F10 * q2 + r2).natDegree ≤ 18 := by
    calc (F10 * q2 + r2).natDegree ≤ max (F10 * q2).natDegree r2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [r1, LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5, q2, r2, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
lemma prod3 : r2 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 = F10 * q3 + r3 := by
  have hA : r2.natDegree ≤ 9 := by unfold r2; compute_degree!
  have hB : LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0; compute_degree!
  have hQ : q3.natDegree ≤ 8 := by unfold q3; compute_degree!
  have hR : r3.natDegree ≤ 9 := by unfold r3; compute_degree!
  have hL : (r2 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0).natDegree ≤ 18 := by
    calc (r2 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0).natDegree ≤ r2.natDegree + LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * q3).natDegree ≤ 18 := by
    calc (F10 * q3).natDegree ≤ F10.natDegree + q3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hRn : (F10 * q3 + r3).natDegree ≤ 18 := by
    calc (F10 * q3 + r3).natDegree ≤ max (F10 * q3).natDegree r3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [r2, LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0, q3, r3, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
theorem chain1249 : F10 ∣ X ^ 1249 - r3 := by
  have h10 := LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.chain 10 (by norm_num)
  have h7 := LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.chain 7 (by norm_num)
  have h6 := LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.chain 6 (by norm_num)
  have h5 := LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.chain 5 (by norm_num)
  have h0 := LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.chain 0 (by norm_num)
  have h1152 : F10 ∣ X ^ 1152 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 := by
    have := helper2 h10 h7
    simpa [LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.F, pow_add] using this
  have h1152r : F10 ∣ X ^ 1152 - r0 := helper1 h1152 (by simpa using prod0)
  have h1216 : F10 ∣ X ^ 1216 - r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 := by
    have := helper2 h1152r h6
    simpa [LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.F, pow_add] using this
  have h1216r : F10 ∣ X ^ 1216 - r1 := helper1 h1216 (by simpa using prod1)
  have h1248 : F10 ∣ X ^ 1248 - r1 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 := by
    have := helper2 h1216r h5
    simpa [LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.F, pow_add] using this
  have h1248r : F10 ∣ X ^ 1248 - r2 := helper1 h1248 (by simpa using prod2)
  have h1249 : F10 ∣ X ^ 1249 - r2 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 := by
    have := helper2 h1248r h0
    simpa [LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.F, pow_add] using this
  exact helper1 h1249 (by simpa using prod3)
#print axioms chain1249
end LeanFormal.IUT.XiFPaper.S2585Q1249AltActualAdapted
end
