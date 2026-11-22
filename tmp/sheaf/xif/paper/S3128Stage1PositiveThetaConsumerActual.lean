import tmp.sheaf.xif.paper.GlobalPositiveThetaHullLogVolumeActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PositiveThetaConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem S3128Stage1PositiveTheta_perPlace_eq_neg
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) (v : V) :
    thetaHullPositiveLogVolumeAt (I := I) n v =
      -(I.theaterAt (n.val : Int) 0).thetaPacket.logVolume :=
  thetaHullPositiveLogVolumeAt_eq (I := I) n v

theorem S3128Stage1PositiveTheta_global_eq_sum
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    globalThetaHullPositiveLogVolume (I := I) R n =
      ∑ v : V, thetaHullPositiveLogVolumeAt (I := I) n v :=
  globalThetaHullPositiveLogVolume_eq (I := I) R n

noncomputable def S3128Stage1PositiveThetaData
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    GlobalPositiveThetaHullLogVolumeData (I := I) R n :=
  globalPositiveThetaHullLogVolumeData (I := I) R n

#check S3128Stage1PositiveTheta_perPlace_eq_neg
#check S3128Stage1PositiveTheta_global_eq_sum
#check S3128Stage1PositiveThetaData
end LeanFormal.IUT.XiFPaper.S3128Stage1PositiveThetaConsumerActual