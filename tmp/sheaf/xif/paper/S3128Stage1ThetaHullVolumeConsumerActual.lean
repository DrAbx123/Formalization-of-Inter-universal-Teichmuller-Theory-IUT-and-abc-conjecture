import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ThetaHullVolumeConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

theorem S3128Stage1ThetaHullVolume_image_le_hull (v : V) :
    thetaImageVolumeAt (I := I) R n v ≤
      thetaHullVolumeAt (I := I) R n v :=
  thetaImageVolumeAt_le_hullVolumeAt (I := I) R n v

theorem S3128Stage1ThetaHullVolume_hull_eq :
    globalThetaHullLogVolume (I := I) R n =
      ∑ v : V, Real.log
        (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal :=
  globalThetaHullLogVolume_eq (I := I) R n

theorem S3128Stage1ThetaHullVolume_image_eq :
    globalThetaImageLogVolume (I := I) R n =
      ∑ v : V, Real.log
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v (R v) n)).toReal :=
  globalThetaImageLogVolume_eq (I := I) R n

theorem S3128Stage1ThetaHullVolume_qPilot_eq :
    globalQPilotLogVolume (I := I) = I.qPilotSignedLogVolume :=
  globalQPilotLogVolume_eq (I := I)

noncomputable def S3128Stage1ThetaHullVolumeData :
    GlobalThetaPilotHullLogVolumeData (I := I) R n :=
  globalThetaPilotHullLogVolumeData (I := I) R n

#check S3128Stage1ThetaHullVolume_image_le_hull
#check S3128Stage1ThetaHullVolume_hull_eq
#check S3128Stage1ThetaHullVolume_image_eq
#check S3128Stage1ThetaHullVolume_qPilot_eq
#check S3128Stage1ThetaHullVolumeData
end LeanFormal.IUT.XiFPaper.S3128Stage1ThetaHullVolumeConsumerActual