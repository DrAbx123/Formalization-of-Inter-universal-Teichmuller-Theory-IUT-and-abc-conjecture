import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2597a0BStepActual

open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual


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

lemma B0_eq_A4 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 = LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 := rfl

lemma hB0 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 := by
  rw [B0_eq_A4]
  exact hA4

lemma hstepB0 : B0 * B0 = F10 * Qbstep0 + B1 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep0,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep0,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep0,
    B0, B1, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep0
