import tmp.sheaf.xif.paper.S2807SG3bScalarActual
import tmp.sheaf.xif.paper.S3018C3TensorPacketLogVolumeFormula

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2807SG3bScalarActual
open LeanFormal.IUT.XiFPaper.S3018C3TensorPacketLogVolumeFormula
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3025ActualThetaUpperAudit

/-!
S3025 audit: the actual theta upper cannot be built from the current tree
without an upper input.

* S2807SG3bScalarActual.S2807_upperGap_of_packetLogVolume_le
  requires BOTH:
    hpacket : actualC3LogShellTensorLogVolume ... = packetLogVolume
    hscalar : -packetLogVolume <= CThetaPaper ... * paperQAbsLog ...
  The second is exactly the theta upper; it is an input, not constructed.
* S3018C3TensorPacketLogVolumeFormula is an iff formula for the packet log
  volume, not an inequality against CThetaPaper.
* Old Stage1 shadow explicit_estimates_to_theorem110_rhs is a structure
  field, not a source theorem; importing it would just move the upper into a
  field, forbidden by the task.

Therefore no actual theta upper is produced here.  The exact first missing
object is a proved inequality
  - actualC3LogShellTensorLogVolume ... <= CThetaPaper ... * paperQAbsLog ...
with the packet identity supplied independently.
-/

#check S3018C3TensorPacketLogVolumeFormula
#check S3018C3TensorPacketLogVolumeFormula_iff
#check S2807_upperGap_of_packetLogVolume_le

def S3025MissingThetaUpperScalar
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (D : N8Closure.C3Actual.SourcePilotRegionDonors
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat))
    (logQ dmod dFpd fFpd eStar etaPrm : Real) : Prop :=
  - actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D) <=
    CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
      paperQAbsLog fiveLabel logQ

#check S3025MissingThetaUpperScalar

end LeanFormal.IUT.XiFPaper.S3025ActualThetaUpperAudit
end