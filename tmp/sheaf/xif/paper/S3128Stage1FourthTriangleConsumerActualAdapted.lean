import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthTriangleConsumerActualAdapted
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual comparison data exposed as the Stage 1 fourth-triangle consumer. -/
noncomputable def S3128Stage1FourthTriangleConsumerData :
    GlobalHullQPilotComparisonData (I := I) R n :=
  globalHullQPilotComparisonData

theorem S3128Stage1FourthTriangleConsumerData_qPilotMagnitude :
    (S3128Stage1FourthTriangleConsumerData (I := I) R n).qPilotMagnitude =
      -I.qPilotSignedLogVolume :=
  rfl

theorem S3128Stage1FourthTriangleConsumerData_hullLogVolume :
    (S3128Stage1FourthTriangleConsumerData (I := I) R n).hullLogVolume =
      globalThetaHullLogVolume (I := I) R n :=
  rfl

theorem S3128Stage1FourthTriangleConsumer_comparison_iff :
    qPilotThetaHullComparison (I := I) R n ↔
      globalThetaHullLogVolume (I := I) R n <=
        qPilotMagnitude (I := I) :=
  qPilotThetaHullComparison_iff

theorem S3128Stage1FourthTriangleConsumer_condition_iff :
    GlobalComparisonCondition (I := I) R n ↔
      qPilotThetaHullComparison (I := I) R n :=
  GlobalComparisonCondition_iff

#check S3128Stage1FourthTriangleConsumerData
#check S3128Stage1FourthTriangleConsumerData_qPilotMagnitude
#check S3128Stage1FourthTriangleConsumer_comparison_iff
#check S3128Stage1FourthTriangleConsumer_condition_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthTriangleConsumerActualAdapted