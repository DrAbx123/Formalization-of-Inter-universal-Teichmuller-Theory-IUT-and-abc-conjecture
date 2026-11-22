import tmp.sheaf.xif.paper.S2597bHBez4Actual
import tmp.sheaf.xif.paper.S2564Batch5CorrectActual
import tmp.sheaf.xif.paper.S2571Bezout5Actual
import tmp.sheaf.xif.paper.S2598d0DStepActual
import tmp.sheaf.xif.paper.S2598d1DStepActual
import tmp.sheaf.xif.paper.S2598d2DStepActual
import tmp.sheaf.xif.paper.S2598d3DStepActual
import tmp.sheaf.xif.paper.S2598d4DStepActual
import tmp.sheaf.xif.paper.S2598d5DStepActual
import tmp.sheaf.xif.paper.S2598d6DStepActual
import tmp.sheaf.xif.paper.S2598d7DStepActual
import tmp.sheaf.xif.paper.S2598d8DStepActual
import tmp.sheaf.xif.paper.S2598d9DStepActual
import tmp.sheaf.xif.paper.S2598e0EStepActual
import tmp.sheaf.xif.paper.S2598e1EStepActual
import tmp.sheaf.xif.paper.S2598e2EStepActual
import tmp.sheaf.xif.paper.S2598e3EStepActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598bHBez5Actual
open LeanFormal.IUT.XiFPaper.S2597bHBez4Actual

private lemma dvd_sq_step {a : Nat} {U V Q : (ZMod 1249)[X]}
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
  have hpow : (X : (ZMod 1249)[X]) ^ (2 * a) = X ^ a * X ^ a := by rw [show 2 * a = a + a by omega, pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ a - V = ((X : (ZMod 1249)[X]) ^ a * X ^ a - U * U) + (U * U - V) := by ring
  rw [hpow, hEq]
  exact hsum

private lemma dvd_mul_step {a b : Nat} {U B V Q : (ZMod 1249)[X]}
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

lemma D0_eq_C4 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 = LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 := rfl
lemma E0_eq_D10 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0 = LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10 := rfl

theorem hE4 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249*1249*1249*1249*1249) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4 := by
  have hD0 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249*1249*1249*1249) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 := by
    have hD0eq : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 = LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 := rfl
    rw [hD0eq]
    exact LeanFormal.IUT.XiFPaper.S2597bHBez4Actual.hC4
  have hD1 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*2) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep0 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 := by
      simpa only [S2598d0DStepActual.F10] using S2598d0DStepActual.hstepD0
    have h := dvd_sq_step (a := 1249*1249*1249*1249) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep0) hD0 hs
    simpa [show 2*(1249*1249*1249*1249) = (1249*1249*1249*1249)*2 by ring] using h
  have hD2 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*4) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep1 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 := by
      simpa only [S2598d1DStepActual.F10] using S2598d1DStepActual.hstepD1
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*2) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep1) hD1 hs
    simpa [show 2*((1249*1249*1249*1249)*2) = (1249*1249*1249*1249)*4 by ring] using h
  have hD3 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*8) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep2 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 := by
      simpa only [S2598d2DStepActual.F10] using S2598d2DStepActual.hstepD2
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*4) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep2) hD2 hs
    simpa [show 2*((1249*1249*1249*1249)*4) = (1249*1249*1249*1249)*8 by ring] using h
  have hD4 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*16) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep3 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 := by
      simpa only [S2598d3DStepActual.F10] using S2598d3DStepActual.hstepD3
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*8) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep3) hD3 hs
    simpa [show 2*((1249*1249*1249*1249)*8) = (1249*1249*1249*1249)*16 by ring] using h
  have hD5 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*32) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep4 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 := by
      simpa only [S2598d4DStepActual.F10] using S2598d4DStepActual.hstepD4
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*16) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep4) hD4 hs
    simpa [show 2*((1249*1249*1249*1249)*16) = (1249*1249*1249*1249)*32 by ring] using h
  have hD6 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*64) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep5 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 := by
      simpa only [S2598d5DStepActual.F10] using S2598d5DStepActual.hstepD5
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*32) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep5) hD5 hs
    simpa [show 2*((1249*1249*1249*1249)*32) = (1249*1249*1249*1249)*64 by ring] using h
  have hD7 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*128) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep6 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 := by
      simpa only [S2598d6DStepActual.F10] using S2598d6DStepActual.hstepD6
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*64) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep6) hD6 hs
    simpa [show 2*((1249*1249*1249*1249)*64) = (1249*1249*1249*1249)*128 by ring] using h
  have hD8 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*256) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep7 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 := by
      simpa only [S2598d7DStepActual.F10] using S2598d7DStepActual.hstepD7
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*128) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep7) hD7 hs
    simpa [show 2*((1249*1249*1249*1249)*128) = (1249*1249*1249*1249)*256 by ring] using h
  have hD9 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*512) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep8 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 := by
      simpa only [S2598d8DStepActual.F10] using S2598d8DStepActual.hstepD8
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*256) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep8) hD8 hs
    simpa [show 2*((1249*1249*1249*1249)*256) = (1249*1249*1249*1249)*512 by ring] using h
  have hD10 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*1024) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep9 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10 := by
      simpa only [S2598d9DStepActual.F10] using S2598d9DStepActual.hstepD9
    have h := dvd_sq_step (a := (1249*1249*1249*1249)*512) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10) (Q := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep9) hD9 hs
    simpa [show 2*((1249*1249*1249*1249)*512) = (1249*1249*1249*1249)*1024 by ring] using h
  have hE0 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*1024) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0 := by
    have hE0eq : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0 = LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10 := rfl
    rw [hE0eq]
    exact hD10
  have hE1 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*1152) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep0 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1 := by
      simpa only [S2598e0EStepActual.F10] using S2598e0EStepActual.hstepE0
    have h := dvd_mul_step (a := (1249*1249*1249*1249)*1024) (b := (1249*1249*1249*1249)*128) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0) (B := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1) hE0 hD7 hs
    simpa [show (1249*1249*1249*1249)*1024 + (1249*1249*1249*1249)*128 = (1249*1249*1249*1249)*1152 by ring] using h
  have hE2 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*1216) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep1 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2 := by
      simpa only [S2598e1EStepActual.F10] using S2598e1EStepActual.hstepE1
    have h := dvd_mul_step (a := (1249*1249*1249*1249)*1152) (b := (1249*1249*1249*1249)*64) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1) (B := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2) hE1 hD6 hs
    simpa [show (1249*1249*1249*1249)*1152 + (1249*1249*1249*1249)*64 = (1249*1249*1249*1249)*1216 by ring] using h
  have hE3 : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*1248) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep2 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3 := by
      simpa only [S2598e2EStepActual.F10] using S2598e2EStepActual.hstepE2
    have h := dvd_mul_step (a := (1249*1249*1249*1249)*1216) (b := (1249*1249*1249*1249)*32) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2) (B := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3) hE2 hD5 hs
    simpa [show (1249*1249*1249*1249)*1216 + (1249*1249*1249*1249)*32 = (1249*1249*1249*1249)*1248 by ring] using h
  have hE4' : LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249*1249*1249*1249)*1249) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4 := by
    have hs : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep3 + LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4 := by
      simpa only [S2598e3EStepActual.F10] using S2598e3EStepActual.hstepE3
    have h := dvd_mul_step (a := (1249*1249*1249*1249)*1248) (b := 1249*1249*1249*1249) (U := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3) (B := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0) (V := LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4) hE3 hD0 hs
    simpa [show (1249*1249*1249*1249)*1248 + 1249*1249*1249*1249 = 1249*1249*1249*1249*1249 by ring] using h
  simpa [show (1249*1249*1249*1249)*1249 = 1249*1249*1249*1249*1249 by ring] using hE4'

theorem hbez5 : ∃ A B : (ZMod 1249)[X], A * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 + B * ((X : (ZMod 1249)[X]) ^ (1249*1249*1249*1249*1249) - X) = 1 := by
  obtain ⟨q, hq⟩ := hE4
  refine ⟨LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.A5 - LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.B5 * q, LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.B5, ?_⟩
  have hS : LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.S5 = LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4 - X := by
    ext n
    by_cases hn : n ≤ 9
    · interval_cases n <;> (simp [LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.S5, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4, Polynomial.coeff_sub, Polynomial.coeff_X] <;> decide)
    · have h1 : LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.S5.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.S5.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.S5; compute_degree!
        omega
      have h2 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4; compute_degree!
        omega
      have hn0 : n ≠ 0 := by omega
      simp [Polynomial.coeff_sub, h1, h2, Polynomial.coeff_X, hn0]
      omega
  calc
    (LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.A5 - LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.B5 * q) * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 + LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.B5 * ((X : (ZMod 1249)[X]) ^ (1249*1249*1249*1249*1249) - X)
        = LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.A5 * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 + LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.B5 * LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.S5 := by
          rw [hS]
          rw [show (X : (ZMod 1249)[X]) ^ (1249*1249*1249*1249*1249) - X = ((X : (ZMod 1249)[X]) ^ (1249*1249*1249*1249*1249) - LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4) + (LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4 - X) by ring, hq]
          ring
    _ = 1 := LeanFormal.IUT.XiFPaper.S2571Bezout5Actual.bezout5

end LeanFormal.IUT.XiFPaper.S2598bHBez5Actual
end
