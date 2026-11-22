import tmp.sheaf.xif.paper.S3016StepVQPilotIdentificationActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol

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
open LeanFormal.IUT.XiFPaper.S3016StepVQPilotIdentificationActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3019StepVQPilotIdentificationProofActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (a b c : Nat)

/-- Exact reduction of the identification target to the log/sum equality. -/
theorem S3019_target_iff_log_sum :
    S3016IdentificationTarget T a b c ↔
      Real.log
          ((FractionalIdeal.absNorm
            (qPilotLineBundleExtended (l := S2771FiveLabel)
              (S2752J S2771FiveLabel a b c)) : Rat) : Real) =
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold S3016IdentificationTarget S3016StepVQPilot S3016WeightedGlobalQPilot
  rw [S2736QPilotLineBundleLogVolume_eq, NativeGlobalQPilotNormalizedLogVolumeActual.nativeGlobalQPilotNormalizedLogMagnitude_eq]

/-- The identification target is purely the displayed log/sum equality; no
side condition is hidden. -/
theorem S3019_identificationTarget_iff_sum :
    S3016IdentificationTarget T a b c ↔
      S2736QPilotLineBundleLogVolume (l := S2771FiveLabel)
          (S2752J S2771FiveLabel a b c) =
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold S3016IdentificationTarget S3016StepVQPilot S3016WeightedGlobalQPilot
  rw [NativeGlobalQPilotNormalizedLogVolumeActual.nativeGlobalQPilotNormalizedLogMagnitude_eq]

/-- The two sides are independent: Step V side varies with (a,b,c), global side
depends only on T.  Exact missing bridge: a theorem identifying
qPilotLineBundleExtended absNorm log with the weighted native sum. -/
def S3019MissingBridge : Prop :=
  ∀ (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (a b c : Nat),
    S3016IdentificationTarget T a b c

#check S3019_target_iff_log_sum
#check S3019_identificationTarget_iff_sum
#check S3019MissingBridge

end LeanFormal.IUT.XiFPaper.S3019StepVQPilotIdentificationProofActual
end