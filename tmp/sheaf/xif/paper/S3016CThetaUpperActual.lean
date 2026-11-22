import tmp.sheaf.xif.paper.S3016StepVQPilotIdentificationActual
import tmp.sheaf.xif.paper.S2959HalfIQHullCThetaUpperActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S3016StepVQPilotIdentificationActual
open LeanFormal.IUT.XiFPaper.S2959HalfIQHullCThetaUpperActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3016CThetaUpperActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (a b c : Nat)

/-- Interface connecting the Step V q-pilot, the weighted global q-pilot, and
the CThetaPaper upper bound.  All numerical fields are actual or explicitly
identified; no inequality is assumed. -/
structure S3016CThetaUpperInterface where
  stepVLogMagnitude : Real
  stepVLogMagnitude_eq : stepVLogMagnitude = S3016StepVQPilot a b c
  globalLogMagnitude : Real
  globalLogMagnitude_eq : globalLogMagnitude = S3016WeightedGlobalQPilot T
  identification : stepVLogMagnitude = globalLogMagnitude
  thetaSigned : Real
  cthetaPaper : Real
  upper : thetaSigned <= cthetaPaper * |stepVLogMagnitude|

/-- From the interface, the Step V q-pilot log-magnitude is the weighted global
one. -/
theorem S3016CThetaUpperInterface.stepV_eq_global
    (I : S3016CThetaUpperInterface T a b c) :
    S3016StepVQPilot a b c = S3016WeightedGlobalQPilot T := by
  rw [← I.stepVLogMagnitude_eq, I.identification, I.globalLogMagnitude_eq]

/-- From the interface, the stated CThetaPaper upper bound holds. -/
theorem S3016CThetaUpperInterface.upper_bound
    (I : S3016CThetaUpperInterface T a b c) :
    I.thetaSigned <= I.cthetaPaper * |S3016StepVQPilot a b c| := by
  rw [← I.stepVLogMagnitude_eq]
  exact I.upper

#check S3016CThetaUpperInterface
#check S3016CThetaUpperInterface.stepV_eq_global
#check S3016CThetaUpperInterface.upper_bound

end LeanFormal.IUT.XiFPaper.S3016CThetaUpperActual
end