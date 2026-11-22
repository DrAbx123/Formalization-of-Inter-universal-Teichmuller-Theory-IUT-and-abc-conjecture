import tmp.sheaf.xif.paper.S2597a0BChainActual
import tmp.sheaf.xif.paper.S2597a1BChainActual
import tmp.sheaf.xif.paper.S2597a2BChainActual
import tmp.sheaf.xif.paper.S2597a3BChainActual
import tmp.sheaf.xif.paper.S2597a4BChainActual
import tmp.sheaf.xif.paper.S2597a5BChainActual
import tmp.sheaf.xif.paper.S2597a6BChainActual
import tmp.sheaf.xif.paper.S2597a7BChainActual
import tmp.sheaf.xif.paper.S2597a8BChainActual
import tmp.sheaf.xif.paper.S2597a9BChainActual
import tmp.sheaf.xif.paper.S2597c0CStepActual
import tmp.sheaf.xif.paper.S2597c1CStepActual
import tmp.sheaf.xif.paper.S2597c2CStepActual
import tmp.sheaf.xif.paper.S2597c3CStepActual
import tmp.sheaf.xif.paper.S2572Bezout134Actual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual
import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 300000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2597bHBez4Actual


lemma dvd_sq_step {a : Nat} {U V Q : (ZMod 1249)[X]}
    (h : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hstep : U * U = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * Q + V) :
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (2 * a) - V := by
  have h1 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U := by
    have hh : (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U = ((X : (ZMod 1249)[X]) ^ a - U) * X ^ a + U * (X ^ a - U) := by ring
    rw [hh]
    exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right h _)
  have h2 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ U * U - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (2 * a) = X ^ a * X ^ a := by rw [show 2*a=a+a by omega, pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ a - V = ((X : (ZMod 1249)[X]) ^ a * X ^ a - U * U) + (U * U - V) := by ring
  rw [hpow, hEq]
  exact hsum

lemma dvd_mul_step {a b : Nat} {U B V Q : (ZMod 1249)[X]}
    (hU : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hB : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ b - B)
    (hstep : U * B = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * Q + V) :
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (a + b) - V := by
  have h1 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ b - U * B := by
    have hh : (X : (ZMod 1249)[X]) ^ a * X ^ b - U * B = ((X : (ZMod 1249)[X]) ^ a - U) * X ^ b + U * (X ^ b - B) := by ring
    rw [hh]
    exact dvd_add (dvd_mul_of_dvd_left hU _) (dvd_mul_of_dvd_right hB _)
  have h2 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ U * B - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (a + b) = X ^ a * X ^ b := by rw [pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ b - V = ((X : (ZMod 1249)[X]) ^ a * X ^ b - U * B) + (U * B - V) := by ring
  rw [hpow, hEq]
  exact hsum

lemma hB0 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 := S2597a0BChainActual.hB0

lemma hB1 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 2) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep0) (LeanFormal.IUT.XiFPaper.S2597a0BChainActual.hB0) (LeanFormal.IUT.XiFPaper.S2597a0BChainActual.hstepB0)
  simpa [show 2 * (1249 * 1249 * 1249) = 1249 * 1249 * 1249 * 2 by ring] using h

lemma hB2 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 4) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 2) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep1) hB1 (LeanFormal.IUT.XiFPaper.S2597a1BChainActual.hstepB1)
  simpa [show 2 * (1249 * 1249 * 1249 * 2) = 1249 * 1249 * 1249 * 4 by ring] using h

lemma hB3 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 8) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 4) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep2) hB2 (LeanFormal.IUT.XiFPaper.S2597a2BChainActual.hstepB2)
  simpa [show 2 * (1249 * 1249 * 1249 * 4) = 1249 * 1249 * 1249 * 8 by ring] using h

lemma hB4 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 16) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B4 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 8) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B4) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep3) hB3 (LeanFormal.IUT.XiFPaper.S2597a3BChainActual.hstepB3)
  simpa [show 2 * (1249 * 1249 * 1249 * 8) = 1249 * 1249 * 1249 * 16 by ring] using h

lemma hB5 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 32) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 16) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B4) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep4) hB4 (LeanFormal.IUT.XiFPaper.S2597a4BChainActual.hstepB4)
  simpa [show 2 * (1249 * 1249 * 1249 * 16) = 1249 * 1249 * 1249 * 32 by ring] using h

lemma hB6 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 64) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 32) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep5) hB5 (LeanFormal.IUT.XiFPaper.S2597a5BChainActual.hstepB5)
  simpa [show 2 * (1249 * 1249 * 1249 * 32) = 1249 * 1249 * 1249 * 64 by ring] using h

lemma hB7 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 128) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 64) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep6) hB6 (LeanFormal.IUT.XiFPaper.S2597a6BChainActual.hstepB6)
  simpa [show 2 * (1249 * 1249 * 1249 * 64) = 1249 * 1249 * 1249 * 128 by ring] using h

lemma hB8 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 256) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 128) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep7) hB7 (LeanFormal.IUT.XiFPaper.S2597a7BChainActual.hstepB7)
  simpa [show 2 * (1249 * 1249 * 1249 * 128) = 1249 * 1249 * 1249 * 256 by ring] using h

lemma hB9 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 512) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 256) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep8) hB8 (LeanFormal.IUT.XiFPaper.S2597a8BChainActual.hstepB8)
  simpa [show 2 * (1249 * 1249 * 1249 * 256) = 1249 * 1249 * 1249 * 512 by ring] using h

lemma hB10 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1024) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B10 := by
  have h := dvd_sq_step (a := 1249 * 1249 * 1249 * 512) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B10) (Q := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep9) hB9 (LeanFormal.IUT.XiFPaper.S2597a9BChainActual.hstepB9)
  simpa [show 2 * (1249 * 1249 * 1249 * 512) = 1249 * 1249 * 1249 * 1024 by ring] using h

lemma C0_eq_B10 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C0 = LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B10 := rfl
lemma hC0 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1024) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C0 := by
  rw [C0_eq_B10]
  exact hB10

lemma hC1 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1152) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1 := by
  have h := dvd_mul_step (a := 1249 * 1249 * 1249 * 1024) (b := 1249 * 1249 * 1249 * 128) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C0) (B := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1) hC0 hB7 (LeanFormal.IUT.XiFPaper.S2597c0CStepActual.hstepC0)
  simpa [show 1249 * 1249 * 1249 * 1024 + 1249 * 1249 * 1249 * 128 = 1249 * 1249 * 1249 * 1152 by ring] using h

lemma hC2 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1216) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2 := by
  have h := dvd_mul_step (a := 1249 * 1249 * 1249 * 1152) (b := 1249 * 1249 * 1249 * 64) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1) (B := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2) hC1 hB6 (LeanFormal.IUT.XiFPaper.S2597c1CStepActual.hstepC1)
  simpa [show 1249 * 1249 * 1249 * 1152 + 1249 * 1249 * 1249 * 64 = 1249 * 1249 * 1249 * 1216 by ring] using h

lemma hC3 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1248) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3 := by
  have h := dvd_mul_step (a := 1249 * 1249 * 1249 * 1216) (b := 1249 * 1249 * 1249 * 32) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2) (B := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3) hC2 hB5 (LeanFormal.IUT.XiFPaper.S2597c2CStepActual.hstepC2)
  simpa [show 1249 * 1249 * 1249 * 1216 + 1249 * 1249 * 1249 * 32 = 1249 * 1249 * 1249 * 1248 by ring] using h

lemma hC4 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1249) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 := by
  have h := dvd_mul_step (a := 1249 * 1249 * 1249 * 1248) (b := 1249 * 1249 * 1249) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3) (B := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4) hC3 hB0 (LeanFormal.IUT.XiFPaper.S2597c3CStepActual.hstepC3)
  simpa [show 1249 * 1249 * 1249 * 1248 + 1249 * 1249 * 1249 = 1249 * 1249 * 1249 * 1249 by ring] using h

lemma S4_eq_C4 : LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S4 = LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 - X := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;> (simp [LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S4, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4, Polynomial.coeff_sub, Polynomial.coeff_X] <;> decide)
  · have h1 : LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S4.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S4; compute_degree!
      omega
    have h2 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4; compute_degree!
      omega
    have hx : (X : (ZMod 1249)[X]).coeff n = 0 := by rw [coeff_X, if_neg (by omega)]
    rw [h1, coeff_sub, h2, hx, sub_zero]

theorem hbez4 : ∃ A B : (ZMod 1249)[X],
    A * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 + B * ((X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1249) - X) = 1 := by
  obtain ⟨q, hq⟩ := hC4
  refine ⟨LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.A4 - LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B4 * q, LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B4, ?_⟩
  have hq' : (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1249) - X = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * q + (LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 - X) := by
    rw [show (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1249) - X = ((X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1249) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4) + (LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 - X) by ring, hq]
  calc
    (LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.A4 - LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B4 * q) * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 + LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B4 * ((X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249 * 1249) - X)
        = LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.A4 * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 + LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B4 * LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S4 := by rw [S4_eq_C4, hq']; ring
    _ = 1 := LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.bezout4

end LeanFormal.IUT.XiFPaper.S2597bHBez4Actual

end