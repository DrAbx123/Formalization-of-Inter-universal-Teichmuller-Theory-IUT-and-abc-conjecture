import tmp.sheaf.xif.paper.S172QPilotMultiradialImageActual
import tmp.sheaf.xif.paper.PaperC3SourceQHullRelationActual

/-!
# S186: actual q-pilot multiradial base change to the source tensor carrier

The actual base change

  QPilotMultiradialCarrier
    -> (b : Bad) -> SourceQTensorBlock T b

is constructed pointwise by sourceQHullTransport (the identity on the actual
shared carrier).  It transports the image point and its qUnit hull relation.

The existing Ind1/Ind2/Ind3 actions live on ActualTensorPacket /
ActualInd3Stage, not on SourceQTensorBlock.  The tree has no actual map from
SourceQTensorBlock to those action carriers.  That remaining object is recorded
as a typed required base change, not fabricated as an identity map.  No
inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S186QPilotIndBaseChangeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual source tensor carrier, fiberwise over bad places. -/
abbrev QPilotMultiradialSourceQTensorCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) -> SourceQTensorBlock T b

/-- Actual base change from the multiradial Block carrier to the source tensor
carrier: pointwise sourceQHullTransport. -/
noncomputable def QPilotMultiradialToSourceQTensor :
    QPilotMultiradialCarrier (l := l) T ->
      QPilotMultiradialSourceQTensorCarrier T :=
  fun x b => sourceQHullTransport T b (x b)

theorem QPilotMultiradialToSourceQTensor_apply
    (x : QPilotMultiradialCarrier (l := l) T)
    (b : Bad (nativePlaceSelection T)) :
    QPilotMultiradialToSourceQTensor T x b =
      sourceQHullTransport T b (x b) := rfl

/-- The actual image point transports to the source qUnit tensor image. -/
theorem QPilotMultiradialImagePoint_transport
    (b : Bad (nativePlaceSelection T)) :
    QPilotMultiradialToSourceQTensor T
        (QPilotMultiradialImagePoint (l := l) T) b =
      sourceQHullTransport T b
        (genericQPilotImagePoint (G := sourceQGeometry (l := l) T b)) := rfl

/-- The corrected q-pilot fiber hull is exactly the source qUnit hull set on
the same Block carrier. -/
theorem QPilotMultiradialFiberHull_eq_sourceQHullInPaperBlock
    (b : Bad (nativePlaceSelection T)) :
    QPilotMultiradialFiberHull (l := l) T b =
      sourceQHullInPaperBlock T b :=
  rfl

/-- Actual hull relation transported to the corrected source tensor hull. -/
theorem QPilotMultiradialToSourceQTensor_hull
    (x : QPilotMultiradialCarrier (l := l) T)
    (b : Bad (nativePlaceSelection T)) :
    x b ∈ QPilotMultiradialFiberHull (l := l) T b ↔
      QPilotMultiradialToSourceQTensor T x b ∈
        sourceQTensorLambdaOHull T b := by
  rw [QPilotMultiradialToSourceQTensor_apply,
    QPilotMultiradialFiberHull_eq_sourceQHullInPaperBlock T b]
  exact sourceQHullTransport_hull_relation T b (x b)

/-- Exact required base-change/action object.  The action carriers are the
existing ActualTensorPacket / ActualInd3Stage; no identity map is supplied. -/
structure QPilotIndActionBaseChangeGap where
  actionCarrier : Type
  qPilotTensorToAction : QPilotMultiradialSourceQTensorCarrier T -> actionCarrier
  ind1Action : actionCarrier -> actionCarrier
  ind2Action : actionCarrier -> actionCarrier
  ind3Action : actionCarrier -> actionCarrier
  imageCompatibility : Prop
  actionCompatibility : Prop

/-- The exact missing base-change/action-compatibility object. -/
def QPilotIndActionBaseChangeGapRequired : Prop :=
  Nonempty (QPilotIndActionBaseChangeGap T)

end LeanFormal.IUT.XiFPaper.S186QPilotIndBaseChangeActual

end
