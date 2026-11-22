import tmp.sheaf.xif.paper.S64DependentThetaHullActual
import tmp.sheaf.xif.paper.S92NormRatioUnifiedActual
import tmp.sheaf.xif.paper.BadPlaceNormRatioSourceActual

/-!
# S100: the qVFamily norm-instance gap

The normalized qVFamily norm and the default qVFamily norm are two different
norm instances on the same actual completion element.  This file records:

* exact equality criterion: qVFamNormRatio = 1 iff the paper-normalized
  coefficient equals c_norm;
* concrete failure criterion: unequal coefficients imply ratio != 1;
* actual correction bound: the full qPilot/qVFamily discrepancy
    |globalQPilotLog + dependentQVFamWeightedLogMagnitude|
  is bounded by the actual norm-ratio coefficient gap bound.

No unconditional norm-instance equality is asserted.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S100QVFamNormInstanceGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact equality criterion for the norm-instance gap: the ratio is one iff
paperNormalizedCoefficient equals c_norm at b. -/
theorem qVFamNormInstanceGap_iff_paperCoefficient_eq_cNorm
    (b : Bad (nativePlaceSelection T)) :
    QVFamNormInstanceGap T b ↔
      paperNormalizedCoefficient T b = qVFamNormalizedCoefficient T b := by
  rw [← qVFamNormRatio_eq_one_iff T b]
  exact BadPlaceNormRatioSourceActual.qVFamNormRatio_eq_one_iff_paperCoefficient_eq_cNorm T b

/-- If the coefficients differ, the qVFamily norm ratio is not one; this is the
actual form of the norm-instance obstruction on that qVFamily element. -/
theorem qVFamNormRatio_ne_one_of_coefficient_ne
    (b : Bad (nativePlaceSelection T))
    (h : paperNormalizedCoefficient T b ≠ qVFamNormalizedCoefficient T b) :
    qVFamNormRatio T b ≠ 1 := by
  intro hratio
  exact h ((qVFamNormInstanceGap_iff_paperCoefficient_eq_cNorm T b).mp
    ((qVFamNormRatio_eq_one_iff T b).mp hratio))

/-- Conversely, coefficient equality gives the actual norm-instance equality. -/
theorem qVFamNormInstanceGap_of_paperCoefficient_eq_cNorm
    (b : Bad (nativePlaceSelection T))
    (h : paperNormalizedCoefficient T b = qVFamNormalizedCoefficient T b) :
    QVFamNormInstanceGap T b :=
  (qVFamNormInstanceGap_iff_paperCoefficient_eq_cNorm T b).mpr h

/-- The unified norm-ratio correction is bounded by the actual coefficient-gap
bound. -/
theorem abs_normRatioCorrectionSum_le_gapBound :
    |normRatioCorrectionSum T| ≤ normRatioGapBound T := by
  simpa [normRatioGapBound] using
    BadPlaceNormRatioCorrectionActual.abs_normRatioCorrectionSum_le T

/-- Quantified correction bound: the full qPilot/qVFamily discrepancy is bounded
by the actual coefficient-gap bound. -/
theorem abs_globalQPilotLog_add_dependentQVFam_le_gapBound :
    |globalQPilotLog T + dependentQVFamWeightedLogMagnitude T| ≤
      normRatioGapBound T := by
  have h := globalQPilotLog_eq_neg_dependentQVFam_add_normRatioCorrection T
  calc
    |globalQPilotLog T + dependentQVFamWeightedLogMagnitude T|
        = |normRatioCorrectionSum T| := by
          rw [h]
          ring
    _ ≤ normRatioGapBound T := abs_normRatioCorrectionSum_le_gapBound T

/-- Exact condition under which the correction bound is zero. -/
theorem normRatioGapBound_eq_zero_of_coefficient_eq
    (h : ∀ b : Bad (nativePlaceSelection T),
      paperNormalizedCoefficient T b = qVFamNormalizedCoefficient T b) :
    normRatioGapBound T = 0 := by
  unfold normRatioGapBound
  apply Finset.sum_eq_zero
  intro b _
  rw [h b, sub_self, abs_zero, zero_mul, mul_zero]

end LeanFormal.IUT.XiFPaper.S100QVFamNormInstanceGapActual

end
