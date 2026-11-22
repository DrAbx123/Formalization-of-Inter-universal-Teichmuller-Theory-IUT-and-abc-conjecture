/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual

/-!
# A663 (1/2) 1D inverse prime-power scaling (mainline)

Local inverse scaling laws for the root-extension Haar, split out of
`Mzk1CarrierBadInvScaleLawActual` to keep memory low:
`μ(p⁻¹ • S) = (primeFactor)⁻¹ · μS` and `μ((p^e)⁻¹ • S) = ((primeFactor)^e)⁻¹ · μS`.
No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierPrimeInvScalingActual

open scoped Pointwise ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

theorem prime_inv_smul_measure (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S) =
      (ENNReal.ofReal (primeFactor T b))⁻¹ * rootExtensionHaar T b S := by
  have hp_ne : (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)
  have hsm := rootPrime_smul_measure (T := T) (b := b)
    (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S)
  rw [smul_inv_smul₀ hp_ne S] at hsm
  have hfac0 : ENNReal.ofReal (primeFactor T b) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (primeFactor_pos T b)
  have hfacT : ENNReal.ofReal (primeFactor T b) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfac_eq : ENNReal.ofReal (primeFactor T b) =
      ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
        (qVFamTensorP T b) : rootNormedExtension T b)‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := rfl
  rw [hsm, ← hfac_eq]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hfac0 hfacT, one_mul]

theorem prime_pow_inv_smul_measure (e : ℕ) (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        ((((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ e)⁻¹) • S) =
      ((ENNReal.ofReal (primeFactor T b)) ^ e)⁻¹ * rootExtensionHaar T b S := by
  induction e generalizing S with
  | zero => simp
  | succ n ih =>
      have hp_ne : (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)
      have hscalar : (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (n + 1))⁻¹) =
          ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ n)⁻¹ *
            ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) := by
        rw [pow_succ, mul_inv_rev, mul_comm]
      rw [hscalar, mul_smul]
      rw [ih (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S)]
      rw [prime_inv_smul_measure T b]
      have hf0 : ENNReal.ofReal (primeFactor T b) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]
        exact not_le.mpr (primeFactor_pos T b)
      have hfT : ENNReal.ofReal (primeFactor T b) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hfacpow : ((ENNReal.ofReal (primeFactor T b)) ^ (n + 1))⁻¹ =
          ((ENNReal.ofReal (primeFactor T b)) ^ n)⁻¹ *
            (ENNReal.ofReal (primeFactor T b))⁻¹ := by
        rw [pow_succ,
          ENNReal.mul_inv (Or.inl (pow_ne_zero _ hf0)) (Or.inl (ENNReal.pow_ne_top hfT)),
          mul_comm]
      rw [hfacpow, mul_assoc]

/-! ## 2. The Haar factor of the inverse scalar at a bad place -/

end LeanFormal.IUT.XiFPaper.Mzk1CarrierPrimeInvScalingActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierPrimeInvScalingActual.prime_inv_smul_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierPrimeInvScalingActual.prime_pow_inv_smul_measure