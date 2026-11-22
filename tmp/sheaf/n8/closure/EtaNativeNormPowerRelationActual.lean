import tmp.sheaf.n8.closure.EtaFPlaceNormAgreementActualAttempt
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime

/-!
# Eta native norm power relation actual attempt

Production norm_completionMap_pow proves, on the image of the base completion
inside the upper completion,

  native upper norm = (native base norm) ^ relativeCompletionDegree.

The native q is only a FinitePlaceQCandidate (nonzero, valuation < 1) in the
full upper completion.  Production gives no theorem that its carrier lies in
the base-completion image, and even on that image the produced power relation is
between native norms, not between the normalized upper norm and the native
upper norm.

Therefore NativeNormPowerRelation is not actual from the available data:
- exact missing source: q in image(completionMap);
- exact missing comparison: normalized upper norm vs native upper norm on that
  image.

No arbitrary relation or image membership is assumed.
-/

set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNativeNormPowerRelationActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaFPlaceLogNormAgreementActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Base Fmod completion underlying the relative completion map. -/
abbrev BaseCompletionX : Type _ :=
  Completion (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceAtPrime X).val)

/-- Exact source condition: the native q lies in the base-completion image. -/
def QInBaseImage : Prop :=
  ∃ y : BaseCompletionX X,
    completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceAtPrime X).val y =
      (C9QPilotRegion.nativeQ X).q

/-- Actual production norm transport on the base-completion image. -/
theorem baseImage_norm_pow
    (y : BaseCompletionX X) (hy : y ≠ 0) :
    ‖completionMap (k := X.S.arithmetic.Fmod)
        (nativeFPlaceAtPrime X).val y‖ =
      ‖y‖ ^ relDegree X := by
  simpa [relDegree] using
    norm_completionMap_pow (k := X.S.arithmetic.Fmod)
      (K := X.S.arithmetic.F) (nativeFPlaceAtPrime X).val y hy

/-- Even on the base-completion image, the produced power relation is between
native norms; the normalized/native comparison is a separate exact gap. -/
def NormalizedNativeComparisonOnImage : Prop :=
  ∀ y : BaseCompletionX X, y ≠ 0 →
    ‖((normalizedCompletionRingEquiv (nativeFPlaceAtPrime X).val).symm
        (completionMap (k := X.S.arithmetic.Fmod)
          (nativeFPlaceAtPrime X).val y))‖ =
      ‖y‖

/-- Exact no-go record: the production base-image transport plus image
membership would still require the normalized/native comparison. -/
def NativeNormPowerRelationProductionNoGo : Prop :=
  QInBaseImage X → NormalizedNativeComparisonOnImage X → NativeNormPowerRelation X

end LeanFormal.IUT.N8Closure.EtaNativeNormPowerRelationActual
