import tmp.sheaf.xif.paper.S3025ActualThetaUpperAudit
import tmp.sheaf.xif.paper.S2990ActualDFpdActual
import tmp.sheaf.xif.paper.S2957IndependentCThetaUpperActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3025ActualThetaUpperAudit
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S2957IndependentCThetaUpperActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2807SG3aActual
open LeanFormal.IUT.XiFPaper.S2807SG3bScalarActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-- The S3025 scalar target, specialized to the actual S2990 dFpd/fFpd. -/
def S3034Hscalar (logQ : Real) (a b c : Nat) : Prop :=
  S3025MissingThetaUpperScalar R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D logQ 0
    S2990DFpd (S2990FFpd a b c) 0 0

/-- S3034 target is exactly the negative-packet scalar inequality. -/
theorem S3034_hscalar_iff (logQ : Real) (a b c : Nat) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D logQ a b c ↔
      -actualC3LogShellTensorLogVolume
        (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat D) <=
        CThetaPaper fiveLabel logQ 0 S2990DFpd (S2990FFpd a b c) 0 0 *
          paperQAbsLog fiveLabel logQ :=
  Iff.rfl

#check S3034Hscalar
#check S3034_hscalar_iff
#print axioms S3034_hscalar_iff

end LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual
end
