/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A669 B3: log-product arithmetic for the inverse bad-prime factors (mainline) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedLogLawB3Actual

open scoped ENNReal BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem log_primeFactor (b : Bad (nativePlaceSelection T)) :
    Real.log (primeFactor T b) =
      - (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
        Real.log ((qVFamTensorP T b : ℕ) : ℝ) := by
  have hp2 : (2 : ℝ) ≤ ((qVFamTensorP T b : ℕ) : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).two_le
  have hp0 : ((qVFamTensorP T b : ℕ) : ℝ) ≠ 0 := by positivity
  unfold primeFactor
  rw [rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p, Real.log_pow, Real.log_inv]
  ring

/-- **B3 (abstract, stage4 form)**: log of the inverse prime-power product. -/
theorem log_inv_prod_primeFactor (e : Bad (nativePlaceSelection T) → Nat) :
    Real.log (((∏ b : Bad (nativePlaceSelection T),
        (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹).toReal)) =
      - ∑ b : Bad (nativePlaceSelection T),
          (e b : ℝ) * Real.log (primeFactor T b) := by
  rw [ENNReal.toReal_prod]
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      (((ENNReal.ofReal (primeFactor T b)) ^ (e b))⁻¹).toReal =
        ((primeFactor T b) ^ (e b))⁻¹ := by
    intro b
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (primeFactor_pos T b).le]
  rw [Finset.prod_congr rfl (fun b _ => hterm b)]
  rw [Finset.prod_inv_distrib, Real.log_inv]
  have hprodlog : Real.log (∏ b : Bad (nativePlaceSelection T),
      (primeFactor T b) ^ (e b)) =
      ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) * Real.log (primeFactor T b) := by
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro b _
      rw [Real.log_pow]
    · intro b _
      exact pow_ne_zero _ (ne_of_gt (primeFactor_pos T b))
  rw [hprodlog]

/-- **B3 (final)**: the same log equals `∑_b e_b d_b log p_b`. -/
theorem log_inv_prod_eq_sum (e : Bad (nativePlaceSelection T) → Nat) :
    Real.log (((∏ b : Bad (nativePlaceSelection T),
        (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹).toReal)) =
      ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
            Real.log ((qVFamTensorP T b : ℕ) : ℝ)) := by
  rw [log_inv_prod_primeFactor]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [log_primeFactor]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedLogLawB3Actual

end