import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3086CorrectedPlaceIndexAttempt

/-- The corrected source place type: selected places of the S2696 two-place
selection, not the rational prime strip. -/
abbrev S3086Selected : Type :=
  Selected (S2696SelectionTwo fiveLabel)

/-- S3086 target: an OriginalInput whose V is the corrected selectedPlaces. -/
def S3086CorrectedPlaceIndex : Prop :=
  Nonempty (OriginalInput.{0, 0, 0, 0, 0} fiveLabel S3086Selected)

#check S3086Selected
#check S3086CorrectedPlaceIndex

end LeanFormal.IUT.XiFPaper.S3086CorrectedPlaceIndexAttempt
end