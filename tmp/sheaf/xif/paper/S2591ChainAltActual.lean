import tmp.sheaf.xif.paper.S2587ProductBAltActual
import tmp.sheaf.xif.paper.S2588ProductCAltActual
import tmp.sheaf.xif.paper.S2589ProductDAltActual
import tmp.sheaf.xif.paper.S2582PowerTwoChainAltActual

/-! # S2591: independent X^1249 chain from Product B/C/D -/

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual
open LeanFormal.IUT.XiFPaper.S2587ProductBAltActual
open LeanFormal.IUT.XiFPaper.S2588ProductCAltActual
open LeanFormal.IUT.XiFPaper.S2586ProductAActual
open LeanFormal.IUT.XiFPaper.S2589ProductDAltActual

namespace LeanFormal.IUT.XiFPaper.S2591ChainAltActual

abbrev F : (ZMod 1249)[X] := S2550F10

private lemma dvd_mul_shift {A B : Nat} {r : (ZMod 1249)[X]}
    (h : F ∣ (X : (ZMod 1249)[X]) ^ A - r) :
    F ∣ (X : (ZMod 1249)[X]) ^ (A + B) - r * (X : (ZMod 1249)[X]) ^ B := by
  have h' : F ∣ ((X : (ZMod 1249)[X]) ^ A - r) * X ^ B :=
    dvd_mul_of_dvd_left h _
  convert h' using 1
  rw [pow_add]
  ring

private lemma dvd_prod_step {A B : Nat} {r s : (ZMod 1249)[X]}
    (h1 : F ∣ (X : (ZMod 1249)[X]) ^ A - r)
    (h2 : F ∣ (X : (ZMod 1249)[X]) ^ B - s) :
    F ∣ (X : (ZMod 1249)[X]) ^ (A + B) - r * s := by
  have h1' : F ∣ ((X : (ZMod 1249)[X]) ^ A - r) * X ^ B :=
    dvd_mul_of_dvd_left h1 _
  have h2' : F ∣ ((X : (ZMod 1249)[X]) ^ B - s) * r :=
    dvd_mul_of_dvd_right h2 _
  have h := dvd_add h1' h2'
  have hEq : ((X : (ZMod 1249)[X]) ^ A - r) * X ^ B +
      ((X : (ZMod 1249)[X]) ^ B - s) * r =
      (X : (ZMod 1249)[X]) ^ (A + B) - r * s := by
    rw [pow_add]
    ring
  rwa [hEq] at h

theorem chain1249 : F ∣ (X : (ZMod 1249)[X]) ^ 1249 - sD := by
  have h10 : F ∣ (X : (ZMod 1249)[X]) ^ 1024 - S2560Batch1CorrectActual.R10 := chain10
  have h7 : F ∣ (X : (ZMod 1249)[X]) ^ 128 - S2560Batch1CorrectActual.R7 := chain7
  have h6 : F ∣ (X : (ZMod 1249)[X]) ^ 64 - S2560Batch1CorrectActual.R6 := chain6
  have h5 : F ∣ (X : (ZMod 1249)[X]) ^ 32 - S2560Batch1CorrectActual.R5 := chain5
  have h0 : F ∣ (X : (ZMod 1249)[X]) ^ 1 - S2560Batch1CorrectActual.R0 := chain0
  have h107 := dvd_prod_step h10 h7
  have h1076 := dvd_prod_step h107 h6
  have h10765 := dvd_prod_step h1076 h5
  have hprod : F ∣ (X : (ZMod 1249)[X]) ^ 1249 -
      S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 * S2560Batch1CorrectActual.R5 * S2560Batch1CorrectActual.R0 := by
    have h := dvd_prod_step h10765 h0
    convert h using 1
  have hsB : sB = rB := rfl
  have hsC : S2589ProductDAltActual.sC = S2588ProductCAltActual.sC := rfl
  have hA : F ∣ S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 - sB := by
    rw [hsB]
    refine ⟨q0 * S2560Batch1CorrectActual.R6 + qB, ?_⟩
    rw [prodB_chain]
    ring
  have hB : F ∣ S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 * S2560Batch1CorrectActual.R5 - sB * S2560Batch1CorrectActual.R5 := by
    have h := dvd_mul_of_dvd_right hA S2560Batch1CorrectActual.R5
    convert h using 1
    ring
  have hC : F ∣ sB * S2560Batch1CorrectActual.R5 - S2588ProductCAltActual.sC := by
    refine ⟨qC, ?_⟩
    rw [prodC]
    ring
  have hAC : F ∣ S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 * S2560Batch1CorrectActual.R5 - S2588ProductCAltActual.sC := by
    have h := dvd_add hB hC
    convert h using 1
    ring
  have hD0 : F ∣ (S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 * S2560Batch1CorrectActual.R5) * S2560Batch1CorrectActual.R0 - S2588ProductCAltActual.sC * S2560Batch1CorrectActual.R0 := by
    have h := dvd_mul_of_dvd_right hAC S2560Batch1CorrectActual.R0
    convert h using 1
    ring
  have hD : F ∣ S2588ProductCAltActual.sC * S2560Batch1CorrectActual.R0 - sD := by
    rw [← hsC]
    refine ⟨C 825, ?_⟩
    rw [prodD]
    ring
  have hprodSD : F ∣ S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 * S2560Batch1CorrectActual.R6 * S2560Batch1CorrectActual.R5 * S2560Batch1CorrectActual.R0 - sD := by
    have h := dvd_add hD0 hD
    convert h using 1
    ring
  have hsum := dvd_add hprod hprodSD
  convert hsum using 1
  ring

#print axioms chain1249

end LeanFormal.IUT.XiFPaper.S2591ChainAltActual
end
