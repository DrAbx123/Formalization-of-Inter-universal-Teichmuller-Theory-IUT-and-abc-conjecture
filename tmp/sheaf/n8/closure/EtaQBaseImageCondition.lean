import tmp.sheaf.n8.closure.EtaQOClassReadoutDegreeCorrected
import tmp.sheaf.n8.closure.EtaNativeNormPowerRelationActual

/-!
# Eta q base-image condition

QInBaseImage and NormalizedNativeComparisonOnImage are not internally derivable
from the current production API.  They are explicit source-admissible inputs:
a source q construction/implementation may provide the base-completion image
point y and the normalized/native comparison on that image.

This file:
- bundles them as QBaseImageCondition;
- proves that QBaseImageCondition implies NativeNormPowerRelation;
- feeds the condition into the corrected qO readout target;
- records the downstream dependency boundary.

No arbitrary image membership is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQBaseImageCondition

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaQOClassReadoutNormalizedActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQOClassReadoutDegreeCorrected
open LeanFormal.IUT.N8Closure.EtaNativeNormPowerRelationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Explicit source-admissible q base-image condition. -/
structure QBaseImageCondition where
  inImage : QInBaseImage X
  comparison : NormalizedNativeComparisonOnImage X

/-- QBaseImageCondition supplies the norm power relation. -/
theorem nativeNormPowerRelation_of_baseImageCondition
    (B : QBaseImageCondition X) :
    NativeNormPowerRelation X := by
  obtain ⟨y, hyq⟩ := B.inImage
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hyq
    exact (C9QPilotRegion.nativeQ X).q_ne_zero hyq.symm
  have hnative : ‖nativeQVal X‖ = ‖y‖ ^ relDegree X := by
    rw [nativeQVal, ← hyq]
    exact baseImage_norm_pow X y hy0
  have hcomp :
      (normalizedCompletionRingEquiv (nativeFPlaceAtPrime X).val).symm
        (completionMap (k := X.S.arithmetic.Fmod)
          (nativeFPlaceAtPrime X).val y) = normalizedQVal X := by
    rw [hyq]
    rfl
  have hnormalized : ‖normalizedQVal X‖ = ‖y‖ := by
    have hnormq : normalizedQVal X =
        (normalizedCompletionRingEquiv (nativeFPlaceAtPrime X).val).symm
          (completionMap (k := X.S.arithmetic.Fmod)
            (nativeFPlaceAtPrime X).val y) := by
      rw [hyq]
      rfl
    rw [hnormq]
    exact B.comparison y hy0
  rw [NativeNormPowerRelation, hnative, hnormalized]

/-- Corrected qO readout target with the source-admissible base-image condition. -/
def CorrectedQOClassReadoutTargetWithSourceCondition
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] : Prop :=
  QBaseImageCondition X → correctedQOClassReadoutAtF X μ = qPilotSignedLog X

/-- Actual downstream check: the corrected qO readout follows from the source
base-image condition plus scaling, normalization and nonzero degrees. -/
theorem correctedQOClassReadoutTargetWithSourceCondition_actual
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ)
    (hd : (Module.finrank ℚ_[nativePrime X] (KfX X) : ℝ) ≠ 0)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    CorrectedQOClassReadoutTargetWithSourceCondition X μ := by
  intro B
  exact correctedQOClassReadoutAtF_eq_qPilot X μ hscale hO
    (nativeNormPowerRelation_of_baseImageCondition X B) hd hrel

/-- Downstream dependency boundary: the source condition replaces the separate
NativeNormPowerRelation gap for the corrected qO readout. -/
theorem correctedQOClassReadoutTarget_sourceDependency
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] :
    CorrectedQOClassReadoutTargetWithSourceCondition X μ ↔
      (QBaseImageCondition X →
        correctedQOClassReadoutAtF X μ = qPilotSignedLog X) :=
  Iff.rfl

end LeanFormal.IUT.N8Closure.EtaQBaseImageCondition
