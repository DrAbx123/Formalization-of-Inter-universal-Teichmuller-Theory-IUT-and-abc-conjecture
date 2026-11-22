/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleProductActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A667 B2/B3: normalization split and log-product arithmetic (mainline)

B2: `s1902NormalizedHaar = s1902HaarScale • productHaar`, so real logs split
additively (pattern copied from shehdd's read-only Sha file).

B3 (following stage4's abstract proof): for `P = ∏_b (ofReal primeFactor_b ^ e_b)⁻¹`,
`Real.log P.toReal = -∑_b e_b log (primeFactor_b)`, and since
`primeFactor_b = p_b^{-d_b}` (p-adic norm), `= ∑_b e_b d_b log p_b`.

B1 (null singletons) stays with hull; no canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogArithmeticActual

open scoped Pointwise ENNReal BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **B2 (raw)**: real log of a scalar-multiplied Haar measure value splits. -/
theorem log_smul_measure_apply
    (c : ENNReal) (mu : Measure (S1902Carrier T)) (S : Set (S1902Carrier T))
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (hS0 : mu S ≠ 0) (hST : mu S ≠ ⊤) :
    Real.log (((c • mu) S).toReal) =
      Real.log c.toReal + Real.log (mu S).toReal := by
  have hsm : ((c • mu) S) = c * mu S := by
    rw [Measure.smul_apply, smul_eq_mul]
  rw [hsm, ENNReal.toReal_mul, Real.log_mul
    (ENNReal.toReal_ne_zero.mpr ⟨hc0, hcT⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨hS0, hST⟩)]

/-- **B2**: `s1902NormalizedHaar` log splits into scale + product Haar logs. -/
theorem s1902_log_split (S : Set (S1902Carrier T))
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T ≠ ⊤)
    (hS0 : rootExtensionProductHaar T S ≠ 0) (hST : rootExtensionProductHaar T S ≠ ⊤) :
    Real.log ((s1902NormalizedHaar T S).toReal) =
      Real.log (s1902HaarScale T).toReal +
        Real.log ((rootExtensionProductHaar T S).toReal) := by
  unfold s1902NormalizedHaar
  exact log_smul_measure_apply T (s1902HaarScale T) (rootExtensionProductHaar T) S
    hc0 hcT hS0 hST

/-- The `primeFactor` is `‖p‖^d = p^{-d}`, so its log is `-d log p`. -/
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

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogArithmeticActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogArithmeticActual.s1902_log_split
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogArithmeticActual.log_inv_prod_primeFactor
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogArithmeticActual.log_inv_prod_eq_sum