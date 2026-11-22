import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ThetaPilotConsumerActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem S3128Stage1ThetaPilot_baseQ_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < baseQReal T b :=
  baseQReal_pos T b

theorem S3128Stage1ThetaPilot_baseQ_lt_one
    (b : Bad (nativePlaceSelection T)) :
    baseQReal T b < 1 :=
  baseQReal_lt_one T b

theorem S3128Stage1ThetaPilot_thetaValue_pos
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    0 < thetaValueFromQ T b j :=
  thetaValueFromQ_pos T b j

theorem S3128Stage1ThetaPilot_log_thetaValue
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    Real.log (thetaValueFromQ T b j) =
      (gaussExponent j.1).toNat * Real.log (baseQReal T b) :=
  log_thetaValueFromQ T b j

theorem S3128Stage1ThetaPilot_local_eq
    (b : Bad (nativePlaceSelection T)) :
    localThetaLogVolume T b =
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        baseQLogMagnitude T b :=
  localThetaLogVolume_eq

theorem S3128Stage1ThetaPilot_global_eq :
    globalThetaPilotLogVolume T =
      ((gaussExponentSum  : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        globalQPilotLogMagnitude T :=
  globalThetaPilotLogVolume_eq

#check S3128Stage1ThetaPilot_baseQ_pos
#check S3128Stage1ThetaPilot_thetaValue_pos
#check S3128Stage1ThetaPilot_local_eq
#check S3128Stage1ThetaPilot_global_eq
end LeanFormal.IUT.XiFPaper.S3128Stage1ThetaPilotConsumerActual