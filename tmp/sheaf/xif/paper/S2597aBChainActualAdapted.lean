import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2597aBChainActualAdapted

open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual


abbrev B0 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0
abbrev B1 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1
abbrev B2 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2
abbrev B3 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3
abbrev B4 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B4
abbrev B5 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5
abbrev B6 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6
abbrev B7 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7
abbrev B8 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8
abbrev B9 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9
abbrev B10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B10

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma dvd_mul_step {a b : Nat} {U B V Q : (ZMod 1249)[X]}
    (hU : F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hB : F10 ∣ (X : (ZMod 1249)[X]) ^ b - B)
    (hstep : U * B = F10 * Q + V) :
    F10 ∣ (X : (ZMod 1249)[X]) ^ (a + b) - V := by
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ b - U * B := by
    have h : (X : (ZMod 1249)[X]) ^ a * X ^ b - U * B = ((X : (ZMod 1249)[X]) ^ a - U) * X ^ b + U * (X ^ b - B) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left hU _) (dvd_mul_of_dvd_right hB _)
  have h2 : F10 ∣ U * B - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (a + b) = X ^ a * X ^ b := by rw [pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ b - V = ((X : (ZMod 1249)[X]) ^ a * X ^ b - U * B) + (U * B - V) := by ring
  rw [hpow, hEq]
  exact hsum

lemma dvd_sq_step {a : Nat} {U V Q : (ZMod 1249)[X]}
    (h : F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hstep : U * U = F10 * Q + V) :
    F10 ∣ (X : (ZMod 1249)[X]) ^ (2 * a) - V := by
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U := by
    have hh : (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U = ((X : (ZMod 1249)[X]) ^ a - U) * X ^ a + U * (X ^ a - U) := by ring
    rw [hh]
    exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right h _)
  have h2 : F10 ∣ U * U - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (2 * a) = X ^ a * X ^ a := by rw [show 2*a=a+a by omega, pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ a - V = ((X : (ZMod 1249)[X]) ^ a * X ^ a - U * U) + (U * U - V) := by ring
  rw [hpow, hEq]
  exact hsum

lemma B0_eq_A4 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 = LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;> (simp [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4] <;> decide)
  · have h1 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0; compute_degree!
      omega
    have h2 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4; compute_degree!
      omega
    rw [h1, h2]

lemma hB0 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 := by
  rw [B0_eq_A4]
  exact hA4

lemma hstepB0 : B0 * B0 = F10 * Qbstep0 + B1 := by
  have hX : B0.natDegree ≤ 9 := by unfold B0; compute_degree!
  have hY : B0.natDegree ≤ 9 := by unfold B0; compute_degree!
  have hQ : Qbstep0.natDegree ≤ 8 := by unfold Qbstep0; compute_degree!
  have hZ : B1.natDegree ≤ 9 := by unfold B1; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B0 * B0).natDegree ≤ 18 := by
    calc (B0 * B0).natDegree ≤ B0.natDegree + B0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep0).natDegree ≤ 18 := by
    calc (F10 * Qbstep0).natDegree ≤ F10.natDegree + Qbstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep0 + B1).natDegree ≤ 18 := by
    calc (F10 * Qbstep0 + B1).natDegree ≤ max (F10 * Qbstep0).natDegree B1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B0, B0, Qbstep0, B1, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB1 : B1 * B1 = F10 * Qbstep1 + B2 := by
  have hX : B1.natDegree ≤ 9 := by unfold B1; compute_degree!
  have hY : B1.natDegree ≤ 9 := by unfold B1; compute_degree!
  have hQ : Qbstep1.natDegree ≤ 8 := by unfold Qbstep1; compute_degree!
  have hZ : B2.natDegree ≤ 9 := by unfold B2; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B1 * B1).natDegree ≤ 18 := by
    calc (B1 * B1).natDegree ≤ B1.natDegree + B1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep1).natDegree ≤ 18 := by
    calc (F10 * Qbstep1).natDegree ≤ F10.natDegree + Qbstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep1 + B2).natDegree ≤ 18 := by
    calc (F10 * Qbstep1 + B2).natDegree ≤ max (F10 * Qbstep1).natDegree B2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B1, B1, Qbstep1, B2, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB2 : B2 * B2 = F10 * Qbstep2 + B3 := by
  have hX : B2.natDegree ≤ 9 := by unfold B2; compute_degree!
  have hY : B2.natDegree ≤ 9 := by unfold B2; compute_degree!
  have hQ : Qbstep2.natDegree ≤ 8 := by unfold Qbstep2; compute_degree!
  have hZ : B3.natDegree ≤ 9 := by unfold B3; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B2 * B2).natDegree ≤ 18 := by
    calc (B2 * B2).natDegree ≤ B2.natDegree + B2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep2).natDegree ≤ 18 := by
    calc (F10 * Qbstep2).natDegree ≤ F10.natDegree + Qbstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep2 + B3).natDegree ≤ 18 := by
    calc (F10 * Qbstep2 + B3).natDegree ≤ max (F10 * Qbstep2).natDegree B3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B2, B2, Qbstep2, B3, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB3 : B3 * B3 = F10 * Qbstep3 + B4 := by
  have hX : B3.natDegree ≤ 9 := by unfold B3; compute_degree!
  have hY : B3.natDegree ≤ 9 := by unfold B3; compute_degree!
  have hQ : Qbstep3.natDegree ≤ 8 := by unfold Qbstep3; compute_degree!
  have hZ : B4.natDegree ≤ 9 := by unfold B4; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B3 * B3).natDegree ≤ 18 := by
    calc (B3 * B3).natDegree ≤ B3.natDegree + B3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep3).natDegree ≤ 18 := by
    calc (F10 * Qbstep3).natDegree ≤ F10.natDegree + Qbstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep3 + B4).natDegree ≤ 18 := by
    calc (F10 * Qbstep3 + B4).natDegree ≤ max (F10 * Qbstep3).natDegree B4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B3, B3, Qbstep3, B4, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB4 : B4 * B4 = F10 * Qbstep4 + B5 := by
  have hX : B4.natDegree ≤ 9 := by unfold B4; compute_degree!
  have hY : B4.natDegree ≤ 9 := by unfold B4; compute_degree!
  have hQ : Qbstep4.natDegree ≤ 8 := by unfold Qbstep4; compute_degree!
  have hZ : B5.natDegree ≤ 9 := by unfold B5; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B4 * B4).natDegree ≤ 18 := by
    calc (B4 * B4).natDegree ≤ B4.natDegree + B4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep4).natDegree ≤ 18 := by
    calc (F10 * Qbstep4).natDegree ≤ F10.natDegree + Qbstep4.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep4 + B5).natDegree ≤ 18 := by
    calc (F10 * Qbstep4 + B5).natDegree ≤ max (F10 * Qbstep4).natDegree B5.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B4, B4, Qbstep4, B5, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB5 : B5 * B5 = F10 * Qbstep5 + B6 := by
  have hX : B5.natDegree ≤ 9 := by unfold B5; compute_degree!
  have hY : B5.natDegree ≤ 9 := by unfold B5; compute_degree!
  have hQ : Qbstep5.natDegree ≤ 8 := by unfold Qbstep5; compute_degree!
  have hZ : B6.natDegree ≤ 9 := by unfold B6; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B5 * B5).natDegree ≤ 18 := by
    calc (B5 * B5).natDegree ≤ B5.natDegree + B5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep5).natDegree ≤ 18 := by
    calc (F10 * Qbstep5).natDegree ≤ F10.natDegree + Qbstep5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep5 + B6).natDegree ≤ 18 := by
    calc (F10 * Qbstep5 + B6).natDegree ≤ max (F10 * Qbstep5).natDegree B6.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B5, B5, Qbstep5, B6, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB6 : B6 * B6 = F10 * Qbstep6 + B7 := by
  have hX : B6.natDegree ≤ 9 := by unfold B6; compute_degree!
  have hY : B6.natDegree ≤ 9 := by unfold B6; compute_degree!
  have hQ : Qbstep6.natDegree ≤ 8 := by unfold Qbstep6; compute_degree!
  have hZ : B7.natDegree ≤ 9 := by unfold B7; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B6 * B6).natDegree ≤ 18 := by
    calc (B6 * B6).natDegree ≤ B6.natDegree + B6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep6).natDegree ≤ 18 := by
    calc (F10 * Qbstep6).natDegree ≤ F10.natDegree + Qbstep6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep6 + B7).natDegree ≤ 18 := by
    calc (F10 * Qbstep6 + B7).natDegree ≤ max (F10 * Qbstep6).natDegree B7.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B6, B6, Qbstep6, B7, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB7 : B7 * B7 = F10 * Qbstep7 + B8 := by
  have hX : B7.natDegree ≤ 9 := by unfold B7; compute_degree!
  have hY : B7.natDegree ≤ 9 := by unfold B7; compute_degree!
  have hQ : Qbstep7.natDegree ≤ 8 := by unfold Qbstep7; compute_degree!
  have hZ : B8.natDegree ≤ 9 := by unfold B8; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B7 * B7).natDegree ≤ 18 := by
    calc (B7 * B7).natDegree ≤ B7.natDegree + B7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep7).natDegree ≤ 18 := by
    calc (F10 * Qbstep7).natDegree ≤ F10.natDegree + Qbstep7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep7 + B8).natDegree ≤ 18 := by
    calc (F10 * Qbstep7 + B8).natDegree ≤ max (F10 * Qbstep7).natDegree B8.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B7, B7, Qbstep7, B8, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB8 : B8 * B8 = F10 * Qbstep8 + B9 := by
  have hX : B8.natDegree ≤ 9 := by unfold B8; compute_degree!
  have hY : B8.natDegree ≤ 9 := by unfold B8; compute_degree!
  have hQ : Qbstep8.natDegree ≤ 8 := by unfold Qbstep8; compute_degree!
  have hZ : B9.natDegree ≤ 9 := by unfold B9; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B8 * B8).natDegree ≤ 18 := by
    calc (B8 * B8).natDegree ≤ B8.natDegree + B8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep8).natDegree ≤ 18 := by
    calc (F10 * Qbstep8).natDegree ≤ F10.natDegree + Qbstep8.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep8 + B9).natDegree ≤ 18 := by
    calc (F10 * Qbstep8 + B9).natDegree ≤ max (F10 * Qbstep8).natDegree B9.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B8, B8, Qbstep8, B9, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepB9 : B9 * B9 = F10 * Qbstep9 + B10 := by
  have hX : B9.natDegree ≤ 9 := by unfold B9; compute_degree!
  have hY : B9.natDegree ≤ 9 := by unfold B9; compute_degree!
  have hQ : Qbstep9.natDegree ≤ 8 := by unfold Qbstep9; compute_degree!
  have hZ : B10.natDegree ≤ 9 := by unfold B10; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
  have hL : (B9 * B9).natDegree ≤ 18 := by
    calc (B9 * B9).natDegree ≤ B9.natDegree + B9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qbstep9).natDegree ≤ 18 := by
    calc (F10 * Qbstep9).natDegree ≤ F10.natDegree + Qbstep9.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qbstep9 + B10).natDegree ≤ 18 := by
    calc (F10 * Qbstep9 + B10).natDegree ≤ max (F10 * Qbstep9).natDegree B10.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  ext n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [B9, B9, Qbstep9, B10, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hB1 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 2) - B1 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 1) (U := B0) (V := B1) (Q := Qbstep0) hB0 hstepB0
  simpa [show 2 * ((1249 * 1249) * 1249 * 1) = (1249 * 1249) * 1249 * 2 by ring] using h

lemma hB2 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 4) - B2 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 2) (U := B1) (V := B2) (Q := Qbstep1) hB1 hstepB1
  simpa [show 2 * ((1249 * 1249) * 1249 * 2) = (1249 * 1249) * 1249 * 4 by ring] using h

lemma hB3 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 8) - B3 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 4) (U := B2) (V := B3) (Q := Qbstep2) hB2 hstepB2
  simpa [show 2 * ((1249 * 1249) * 1249 * 4) = (1249 * 1249) * 1249 * 8 by ring] using h

lemma hB4 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 16) - B4 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 8) (U := B3) (V := B4) (Q := Qbstep3) hB3 hstepB3
  simpa [show 2 * ((1249 * 1249) * 1249 * 8) = (1249 * 1249) * 1249 * 16 by ring] using h

lemma hB5 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 32) - B5 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 16) (U := B4) (V := B5) (Q := Qbstep4) hB4 hstepB4
  simpa [show 2 * ((1249 * 1249) * 1249 * 16) = (1249 * 1249) * 1249 * 32 by ring] using h

lemma hB6 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 64) - B6 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 32) (U := B5) (V := B6) (Q := Qbstep5) hB5 hstepB5
  simpa [show 2 * ((1249 * 1249) * 1249 * 32) = (1249 * 1249) * 1249 * 64 by ring] using h

lemma hB7 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 128) - B7 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 64) (U := B6) (V := B7) (Q := Qbstep6) hB6 hstepB6
  simpa [show 2 * ((1249 * 1249) * 1249 * 64) = (1249 * 1249) * 1249 * 128 by ring] using h

lemma hB8 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 256) - B8 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 128) (U := B7) (V := B8) (Q := Qbstep7) hB7 hstepB7
  simpa [show 2 * ((1249 * 1249) * 1249 * 128) = (1249 * 1249) * 1249 * 256 by ring] using h

lemma hB9 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 512) - B9 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 256) (U := B8) (V := B9) (Q := Qbstep8) hB8 hstepB8
  simpa [show 2 * ((1249 * 1249) * 1249 * 256) = (1249 * 1249) * 1249 * 512 by ring] using h

lemma hB10 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 1024) - B10 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 512) (U := B9) (V := B10) (Q := Qbstep9) hB9 hstepB9
  simpa [show 2 * ((1249 * 1249) * 1249 * 512) = (1249 * 1249) * 1249 * 1024 by ring] using h

end LeanFormal.IUT.XiFPaper.S2597aBChainActualAdapted

end
