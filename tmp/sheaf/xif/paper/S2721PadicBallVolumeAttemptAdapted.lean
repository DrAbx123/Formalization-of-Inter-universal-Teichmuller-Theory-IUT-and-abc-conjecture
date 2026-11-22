import tmp.sheaf.xif.paper.S2721BridgeSkeletonActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.LocalFieldPadicTensor
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2721PadicBallVolumeAttemptAdapted

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

#check Metric.measure_closedBall_pos
#check MeasureTheory.Measure.addHaar_ball
#check MeasureTheory.Measure.addHaar_ball_of_pos
#check MeasureTheory.Measure.addHaar_closedBall
#check MeasureTheory.Measure.addHaar_smul
#check measure_image_add_translate
#check finitePadicTensorCoordinates
#check finitePadicTensorNormedAddCommGroup
#check finitePadicTensorProperSpace

/-- Minimal actual: a nonempty p-adic tensor ball has positive finite Haar measure,
and its measure is independent of the centre by translation invariance. -/
theorem padicTensor_closedBall_measure_pos_lt_top
    (x : qVFamTensorBlock T b) {r : Real} (hr : 0 < r) :
    0 < (Measure.addHaar : Measure (qVFamTensorBlock T b)) (Metric.closedBall x r) ∧
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) (Metric.closedBall x r) < ⊤ := by
  haveI : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (qVFamTensorBlock T b)) :=
    inferInstance
  constructor
  · exact Metric.measure_closedBall_pos (Measure.addHaar : Measure (qVFamTensorBlock T b)) x hr
  · exact (isCompact_closedBall x hr.le).measure_lt_top

/-- Translation invariance of the tensor ball Haar measure. -/
theorem padicTensor_closedBall_measure_translate
    (x y : qVFamTensorBlock T b) (r : Real) :
    (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (Metric.closedBall (x + y) r) =
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) (Metric.closedBall y r) := by
  rw [Metric.closedBall_add]
  exact measure_image_add_translate (Measure.addHaar : Measure (qVFamTensorBlock T b)) x
    (Metric.closedBall y r)

#check padicTensor_closedBall_measure_pos_lt_top
#check padicTensor_closedBall_measure_translate
#print axioms padicTensor_closedBall_measure_pos_lt_top
#print axioms padicTensor_closedBall_measure_translate

end LeanFormal.IUT.XiFPaper.S2721PadicBallVolumeAttemptAdapted
end
