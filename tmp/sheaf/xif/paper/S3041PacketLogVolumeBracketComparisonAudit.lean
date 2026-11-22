import tmp.sheaf.xif.paper.S3034PacketScalarBoundActual
import tmp.sheaf.xif.paper.S3018C3TensorPacketLogVolumeFormula
import tmp.sheaf.xif.paper.S2807SG3bScalarActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual
open LeanFormal.IUT.XiFPaper.S3018C3TensorPacketLogVolumeFormula
open LeanFormal.IUT.XiFPaper.S2807SG3bScalarActual
open LeanFormal.IUT.XiFPaper.S2807SG3aActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3041PacketLogVolumeBracketComparisonAudit

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-!
S3041 audit.

S3018C3TensorPacketLogVolumeFormula is an iff-formula:
  actualC3LogShellTensorLogVolume = profileArithmeticDegree (local haarLogVolume).
It contains no bound against CThetaPaper.

S2807SG3a/SG3b only reduce S2717UpperGap to the global scalar inequality
  -packetLogVolume <= CThetaPaper * paperQAbsLog
and SG3b requires that scalar inequality as hscalar.

The tree contains no termwise/local bound
  -localHaarLogVolume i <= CThetaPaper * weight_i
for the actual C3 tensor indices; therefore the termwise summation route
cannot be completed from existing actual lemmas.  The exact missing datum is an equivalent local scalar bound at every tensor index.
-/

#check S3018C3TensorPacketLogVolumeFormula
#check S3018C3TensorPacketLogVolumeFormula_iff
#check S2807_upperGap_of_packetLogVolume_le
#check S3034Hscalar


end LeanFormal.IUT.XiFPaper.S3041PacketLogVolumeBracketComparisonAudit
end