import tmp.sheaf.xif.paper.S290BlockHaarFactorActual
import tmp.sheaf.xif.paper.RootTensorFactorTransferActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S296BlockScaledHullLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarIsometryActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.S290BlockHaarFactorActual
open LeanFormal.IUT.XiFPaper.S288ThetaScalingHaarFactorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem blockScaledRegion_eq_scaling_image
    (a : rootNormedExtension T b) (ha : a ≠ 0) :
    blockScaledRegion T b a =
      (blockScalingContinuousAddEquiv (T := T) (b := b) a ha) ''
        blockThetaReference T b := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩

theorem blockScaledRegionMeasure_eq_thetaScalingHaarFactor
    (a : rootNormedExtension T b) (ha : a ≠ 0) :
    blockHaar T b (blockScaledRegion T b a) =
      (thetaScalingHaarFactor (T := T) (b := b) a ha : ENNReal) := by
  rw [blockScaledRegion_eq_scaling_image (T := T) (b := b) a ha]
  have h := thetaScalingHaarFactor_spec (T := T) (b := b) a ha
    (S := blockThetaReference T b) measurableSet_closedBall
    (by simpa [blockThetaReference] using
      (isCompact_closedBall (0 : rootTensorBlock T b) 1))
  have h1 : blockHaar T b (blockThetaReference T b) = 1 := by
    simpa [blockThetaReference, blockUnitBall, blockUnitBallPositive] using
      blockUnitBall_measure T b
  simpa [h1] using h

theorem singleScaledRegionMeasure_eq_thetaScalingHaarFactor :
    singleScaledRegionMeasure T b =
      (thetaScalingHaarFactor (T := T) (b := b) (singleLambda T b)
        (singleLambda_ne_zero T b) : ENNReal) := by
  unfold singleScaledRegionMeasure
  rw [singleScaledRegion_eq_component]
  exact blockScaledRegionMeasure_eq_thetaScalingHaarFactor
    (T := T) (b := b) (singleLambda T b) (singleLambda_ne_zero T b)

theorem blockThetaScaledHullMeasure_eq_thetaScalingHaarFactor :
    blockThetaScaledHullMeasure T b =
      (thetaScalingHaarFactor (T := T) (b := b) (singleLambda T b)
        (singleLambda_ne_zero T b) : ENNReal) := by
  rw [blockThetaScaledHullMeasure_eq_single]
  exact singleScaledRegionMeasure_eq_thetaScalingHaarFactor (T := T) (b := b)

theorem blockThetaScaledHullLog_eq_log_thetaScalingHaarFactor :
    blockThetaScaledHullLog T b =
      Real.log ((thetaScalingHaarFactor (T := T) (b := b) (singleLambda T b)
        (singleLambda_ne_zero T b) : ENNReal)).toReal := by
  unfold blockThetaScaledHullLog
  rw [blockThetaScaledHullMeasure_eq_thetaScalingHaarFactor]

/-- Uniformizer scalin region measure is ||pi||^d. -/
theorem blockScaledRegionMeasure_uniformizer_eq_norm_pow :
    blockHaar T b (blockScaledRegion T b
      (rootUniformizerField T b : rootNormedExtension T b)) =
      ENNReal.ofReal
        ((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
          Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [blockScaledRegionMeasure_eq_thetaScalingHaarFactor (T := T) (b := b)
      (rootUniformizerField T b : rootNormedExtension T b)
      (Units.ne_zero (rootUniformizerField T b)),
    thetaScalingHaarFactor_uniformizer_eq_norm_pow (T := T) (b := b)]

/-- Uniformizer scaled region log is log(||pi||^d). -/
theorem blockScaledRegionLog_uniformizer_eq_log_norm_pow :
    Real.log ((blockHaar T b (blockScaledRegion T b
      (rootUniformizerField T b : rootNormedExtension T b))).toReal) =
      Real.log ((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [blockScaledRegionMeasure_uniformizer_eq_norm_pow]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Prime scaled region measure is ||p||^d. -/
theorem blockScaledRegionMeasure_prime_eq_norm_pow :
    blockHaar T b (blockScaledRegion T b
      (rootPrimeFieldUnit T b : rootNormedExtension T b)) =
      ENNReal.ofReal
        ((‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
            (qVFamTensorP T b) : rootNormedExtension T b)‖) ^
          Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [blockScaledRegionMeasure_eq_thetaScalingHaarFactor (T := T) (b := b)
      (rootPrimeFieldUnit T b : rootNormedExtension T b)
      (Units.ne_zero (rootPrimeFieldUnit T b)),
    thetaScalingHaarFactor_prime_eq_norm_pow (T := T) (b := b)]

/-- Prime scaled region log is log(||p||^d). -/
theorem blockScaledRegionLog_prime_eq_log_norm_pow :
    Real.log ((blockHaar T b (blockScaledRegion T b
      (rootPrimeFieldUnit T b : rootNormedExtension T b))).toReal) =
      Real.log ((‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
          (qVFamTensorP T b) : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [blockScaledRegionMeasure_prime_eq_norm_pow]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- single region measure in terms of the actual root Haar factor. -/
theorem singleScaledRegionMeasure_eq_rootHaarFactor :
    singleScaledRegionMeasure T b =
      (rootHaarFactor T b (Units.mk0 (singleLambda T b)
        (singleLambda_ne_zero T b)) : ENNReal) := by
  rw [singleScaledRegionMeasure_eq_thetaScalingHaarFactor]
  change (thetaScalingHaarFactor (T := T) (b := b)
    ((Units.mk0 (singleLambda T b) (singleLambda_ne_zero T b) :
      (rootNormedExtension T b)ˣ) : rootNormedExtension T b)
    (Units.ne_zero _) : ENNReal) = _
  rw [thetaScalingHaarFactor_eq_rootHaarFactor]

/-- Theta scaled hull log in terms of the actual root Haar factor. -/
theorem blockThetaScaledHullLog_eq_log_rootHaarFactor :
    blockThetaScaledHullLog T b =
      Real.log ((rootHaarFactor T b (Units.mk0 (singleLambda T b)
        (singleLambda_ne_zero T b)) : ENNReal)).toReal := by
  rw [blockThetaScaledHullLog_eq_log_thetaScalingHaarFactor]
  change Real.log ((thetaScalingHaarFactor (T := T) (b := b)
    ((Units.mk0 (singleLambda T b) (singleLambda_ne_zero T b) :
      (rootNormedExtension T b)ˣ) : rootNormedExtension T b)
    (Units.ne_zero _) : ENNReal)).toReal = _
  rw [thetaScalingHaarFactor_eq_rootHaarFactor]

end LeanFormal.IUT.XiFPaper.S296BlockScaledHullLogActual
end
