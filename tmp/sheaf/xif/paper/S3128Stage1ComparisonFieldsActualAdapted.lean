import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ComparisonFieldsActualAdapted
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

theorem S3128Stage1Comparison_thetaHullSigned_eq_neg :
    thetaHullSignedLogVolume R n =
      -globalThetaHullLogVolume R n := rfl

theorem S3128Stage1Comparison_qPilotMagnitude_eq_neg :
    qPilotMagnitude =
      -I.qPilotSignedLogVolume := rfl

theorem S3128Stage1Comparison_iff :
    qPilotThetaHullComparison R n ↔
      globalThetaHullLogVolume R n <= qPilotMagnitude :=
  qPilotThetaHullComparison_iff R n

#check S3128Stage1Comparison_thetaHullSigned_eq_neg
#check S3128Stage1Comparison_qPilotMagnitude_eq_neg
#check S3128Stage1Comparison_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1ComparisonFieldsActualAdapted