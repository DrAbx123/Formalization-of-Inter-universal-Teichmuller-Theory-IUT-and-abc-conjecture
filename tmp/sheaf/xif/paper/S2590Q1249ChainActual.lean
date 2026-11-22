import tmp.sheaf.xif.paper.S2582PowerTwoChainAltActual
import tmp.sheaf.xif.paper.S2586ProductAActual
import tmp.sheaf.xif.paper.S2587ProductBActual
import tmp.sheaf.xif.paper.S2588ProductCActual
import tmp.sheaf.xif.paper.S2589ProductDActual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual
open LeanFormal.IUT.XiFPaper.S2586ProductAActual
open LeanFormal.IUT.XiFPaper.S2587ProductBActual
open LeanFormal.IUT.XiFPaper.S2588ProductCActual
open LeanFormal.IUT.XiFPaper.S2589ProductDActual

namespace LeanFormal.IUT.XiFPaper.S2590Q1249ChainActual

abbrev F10 : (ZMod 1249)[X] := S2550F10

lemma dvd_mul_shift {a a' b b' : (ZMod 1249)[X]}
    (ha : F10 ∣ a - a') (hb : F10 ∣ b - b') :
    F10 ∣ a * b - a' * b' := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) (dvd_mul_of_dvd_right hb a')

lemma dvd_prod_step {a b q r : (ZMod 1249)[X]}
    (h : a * b = F10 * q + r) : F10 ∣ a * b - r := by
  refine ⟨q, ?_⟩
  rw [h]
  ring

theorem chain1249 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1249 - rD := by
  have hR10 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1024 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 := by
    simpa [F, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R] using chain10
  have hR7 : F10 ∣ (X : (ZMod 1249)[X]) ^ 128 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 := by
    simpa [F, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R] using chain7
  have hA : F10 ∣ (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 :=
    dvd_mul_shift hR10 hR7
  have hA' : F10 ∣ (X : (ZMod 1249)[X]) ^ 1152 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 := by
    have hpow : (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 = X ^ 1152 := by
      rw [← pow_add]
    simpa [hpow] using hA
  have hprodA : F10 ∣ LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 - r0 := dvd_prod_step prodA
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1152 - r0 := by
    have hsum := dvd_add hA' hprodA
    convert hsum using 1
    ring
  have hR6 : F10 ∣ (X : (ZMod 1249)[X]) ^ 64 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 := by
    simpa [F, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R] using chain6
  have hB : F10 ∣ (X : (ZMod 1249)[X]) ^ 1152 * X ^ 64 - r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 :=
    dvd_mul_shift h1 hR6
  have hB' : F10 ∣ (X : (ZMod 1249)[X]) ^ 1216 - r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 := by
    have hpow : (X : (ZMod 1249)[X]) ^ 1152 * X ^ 64 = X ^ 1216 := by
      rw [← pow_add]
    simpa [hpow] using hB
  have hprodB : F10 ∣ r0 * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 - rB := dvd_prod_step prodB
  have h2 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1216 - rB := by
    have hsum := dvd_add hB' hprodB
    convert hsum using 1
    ring
  have hR5 : F10 ∣ (X : (ZMod 1249)[X]) ^ 32 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 := by
    simpa [F, LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual.R] using chain5
  have hC : F10 ∣ (X : (ZMod 1249)[X]) ^ 1216 * X ^ 32 - rB * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 :=
    dvd_mul_shift h2 hR5
  have hC' : F10 ∣ (X : (ZMod 1249)[X]) ^ 1248 - rB * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 := by
    have hpow : (X : (ZMod 1249)[X]) ^ 1216 * X ^ 32 = X ^ 1248 := by
      rw [← pow_add]
    simpa [hpow] using hC
  have hprodC : F10 ∣ rB * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 - rC := dvd_prod_step prodC
  have h3 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1248 - rC := by
    have hsum := dvd_add hC' hprodC
    convert hsum using 1
    ring
  have hR0 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 := by
    simpa [F, R, pow_one] using chain0
  have hD : F10 ∣ (X : (ZMod 1249)[X]) ^ 1248 * X ^ 1 - rC * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 :=
    dvd_mul_shift h3 hR0
  have hD' : F10 ∣ (X : (ZMod 1249)[X]) ^ 1249 - rC * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 := by
    have hpow : (X : (ZMod 1249)[X]) ^ 1248 * X = X ^ 1249 := by
      rw [← pow_succ]
    simpa [hpow, pow_one] using hD
  have hprodD : F10 ∣ rC * LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 - rD := dvd_prod_step prodD
  have hsum := dvd_add hD' hprodD
  convert hsum using 1
  ring

end LeanFormal.IUT.XiFPaper.S2590Q1249ChainActual
end