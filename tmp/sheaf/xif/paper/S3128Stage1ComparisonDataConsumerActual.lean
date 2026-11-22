import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ComparisonDataConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

theorem S3128Stage1ComparisonData_hullSigned :
    (globalHullQPilotComparisonData (I := I) R n).hullSignedLogVolume =
      thetaHullSignedLogVolume (I := I) R n := rfl

theorem S3128Stage1ComparisonData_qPilotMag :
    (globalHullQPilotComparisonData (I := I) R n).qPilotMagnitude =
      qPilotMagnitude (I := I) := rfl

theorem S3128Stage1ComparisonData_condition :
    (globalHullQPilotComparisonData (I := I) R n).condition =
      qPilotThetaHullComparison (I := I) R n := rfl

#check S3128Stage1ComparisonData_hullSigned
#check S3128Stage1ComparisonData_qPilotMag
#check S3128Stage1ComparisonData_condition
end LeanFormal.IUT.XiFPaper.S3128Stage1ComparisonDataConsumerActual