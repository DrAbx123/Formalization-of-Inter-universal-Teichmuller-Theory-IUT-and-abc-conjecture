import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3016StepVQPilotIdentificationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (a b c : Nat)

/-- Step V q-pilot: the actual q-pilot line-bundle log-volume at the
ABC-support ideal. -/
noncomputable def S3016StepVQPilot : Real :=
  S2736QPilotLineBundleLogVolume (l := S2771FiveLabel)
    (S2752J S2771FiveLabel a b c)

/-- Weighted global q-pilot: the actual native global normalized q-pilot
log-magnitude. -/
noncomputable def S3016WeightedGlobalQPilot : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

/-- Exact identification target between the Step V q-pilot and the weighted
global q-pilot. -/
def S3016IdentificationTarget (a b c : Nat) : Prop :=
  S3016StepVQPilot a b c = S3016WeightedGlobalQPilot T

/-- The same target written with the actual definitions. -/
theorem S3016_identificationTarget_iff :
    S3016IdentificationTarget (T := T) a b c ↔
      S2736QPilotLineBundleLogVolume (l := S2771FiveLabel)
        (S2752J S2771FiveLabel a b c) =
      nativeGlobalQPilotNormalizedLogMagnitude T :=
  Iff.rfl

/-- Exact gap: the identification is not a definitional equality. -/
def S3016IdentificationGap (a b c : Nat) : Prop :=
  S3016IdentificationTarget (T := T) a b c

#check S3016StepVQPilot
#check S3016WeightedGlobalQPilot
#check S3016IdentificationTarget
#check S3016_identificationTarget_iff
#check S3016IdentificationGap

end LeanFormal.IUT.XiFPaper.S3016StepVQPilotIdentificationActual
end