/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedLogLawB2Actual
import tmp.sheaf.xif.paper.Mzk1CorrectedLogLawB3Actual
import tmp.sheaf.xif.paper.Mzk1CorrectedRegionLogLawBlockersActual

/-!
# A669/A672 corrected-region log law: proved unit-region part (mainline)

`s1902LogVolume` unwrap + normalization split (B2) + log arithmetic (B3) + green
unit-region product law give the exact log law on the actual unit region:
`logVol(correctedRegion e '' unitRegion) = logVol unitRegion + ∑_b e_b d_b log p_b`.
Full `CorrectedRegionLogLaw` still needs B1 (null singleton) for the union with the
triple-dependent point; not assumed.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawProvedActual

open scoped Pointwise ENNReal BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedLogLawB2Actual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedLogLawB3Actual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawBlockersActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Unwrap `s1902LogVolume` for finite measures of volume at least `1`. -/
theorem s1902LogVolume_toReal_eq_log (S : Set (S1902Carrier T))
    (hfin : s1902NormalizedHaar T S < ⊤)
    (hpos : 1 ≤ (s1902NormalizedHaar T S).toReal) :
    (s1902LogVolume T S).toReal = Real.log ((s1902NormalizedHaar T S).toReal) := by
  unfold s1902LogVolume
  rw [haarLogVolume_of_lt_top hfin]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg hpos)]

/-- **Proved unit-region log law** for the corrected region. -/
theorem corrected_unitRegion_logLaw (e : Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤) :
    (s1902LogVolume T (badInvScale T e '' s1902UnitRegion T)).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal +
        ∑ b : Bad (nativePlaceSelection T),
          (e b : ℝ) *
            ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
              Real.log ((qVFamTensorP T b : ℕ) : ℝ)) := by
  have hμT_lt : rootExtensionProductHaar T (s1902UnitRegion T) < ⊤ := by
    rw [s1902UnitRegion, rootExtensionProductUnitBall]
    exact (rootExtensionProductHaar_unitBall_pos_lt_top T).2
  have hμT0 : rootExtensionProductHaar T (s1902UnitRegion T) ≠ 0 := by
    rw [s1902UnitRegion, rootExtensionProductUnitBall]
    exact ne_of_gt (rootExtensionProductHaar_unitBall_pos_lt_top T).1
  have hP0 : (∏ b : Bad (nativePlaceSelection T),
      (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hPT : (∏ b : Bad (nativePlaceSelection T),
      (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.prod_lt_top
    intro b _
    apply ENNReal.inv_lt_top.mpr
    exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (primeFactor_pos T b)) _
  have hPge : 1 ≤ (∏ b : Bad (nativePlaceSelection T),
      (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) := by
    refine Finset.one_le_prod ?_
    intro b _
    rw [ENNReal.one_le_inv]
    exact pow_le_one₀ (le_of_lt (ENNReal.ofReal_pos.mpr (primeFactor_pos T b)))
      (le_of_lt (ENNReal.ofReal_lt_one.mpr (primeFactor_lt_one T b)))
  have hmeas : rootExtensionProductHaar T (badInvScale T e '' s1902UnitRegion T) =
      (∏ b : Bad (nativePlaceSelection T),
        (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (s1902UnitRegion T) := corrected_unitRegion_measure T e
  have hμc_lt : rootExtensionProductHaar T
      (badInvScale T e '' s1902UnitRegion T) < ⊤ := by
    rw [hmeas]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hPT) hμT_lt
  have hμc0 : rootExtensionProductHaar T
      (badInvScale T e '' s1902UnitRegion T) ≠ 0 := by
    rw [hmeas]
    exact mul_ne_zero hP0 hμT0
  have hfinU : s1902NormalizedHaar T (s1902UnitRegion T) < ⊤ := by
    unfold s1902NormalizedHaar
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hcT hμT_lt
  have hfinC : s1902NormalizedHaar T
      (badInvScale T e '' s1902UnitRegion T) < ⊤ := by
    unfold s1902NormalizedHaar
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hcT hμc_lt
  have hSU := s1902_log_split T (s1902UnitRegion T) hc0 (ne_of_lt hcT) hμT0 (ne_of_lt hμT_lt)
  have hSC := s1902_log_split T (badInvScale T e '' s1902UnitRegion T) hc0 (ne_of_lt hcT) hμc0 (ne_of_lt hμc_lt)
  have hunit : s1902NormalizedHaar T (s1902UnitRegion T) = ENNReal.ofReal (Real.exp 1) :=
    s1902NormalizedHaar_unitRegion T
  have hposU : 1 ≤ (s1902NormalizedHaar T (s1902UnitRegion T)).toReal := by
    rw [hunit, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos 1))]
    exact Real.one_le_exp_iff.mpr (by norm_num)
  have hPmul : rootExtensionProductHaar T (s1902UnitRegion T) ≤
      (∏ b : Bad (nativePlaceSelection T),
        (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (s1902UnitRegion T) := by
    calc rootExtensionProductHaar T (s1902UnitRegion T)
        = 1 * rootExtensionProductHaar T (s1902UnitRegion T) := (one_mul _).symm
      _ ≤ (∏ b : Bad (nativePlaceSelection T),
            (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
            rootExtensionProductHaar T (s1902UnitRegion T) := by
          exact mul_le_mul_right' hPge _
  have hge : s1902NormalizedHaar T (s1902UnitRegion T) ≤ s1902NormalizedHaar T
      (badInvScale T e '' s1902UnitRegion T) := by
    unfold s1902NormalizedHaar
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, hmeas]
    exact mul_le_mul_left' hPmul _
  have hposC : 1 ≤ (s1902NormalizedHaar T
      (badInvScale T e '' s1902UnitRegion T)).toReal := by
    calc 1 ≤ (s1902NormalizedHaar T (s1902UnitRegion T)).toReal := hposU
      _ ≤ (s1902NormalizedHaar T
          (badInvScale T e '' s1902UnitRegion T)).toReal := by
          exact ENNReal.toReal_mono (ne_of_lt hfinC) hge
  have hunwrapU := s1902LogVolume_toReal_eq_log T (s1902UnitRegion T) hfinU hposU
  have hunwrapC := s1902LogVolume_toReal_eq_log T
    (badInvScale T e '' s1902UnitRegion T) hfinC hposC
  rw [hunwrapC, hunwrapU, hSC, hSU]
  rw [hmeas, ENNReal.toReal_mul, Real.log_mul
    (ENNReal.toReal_ne_zero.mpr ⟨hP0, hPT⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨hμT0, ne_of_lt hμT_lt⟩)]
  have hPlog := log_inv_prod_eq_sum T e
  rw [hPlog]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawProvedActual

end