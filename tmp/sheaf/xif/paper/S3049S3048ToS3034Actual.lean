import tmp.sheaf.xif.paper.S3048MeasureLowerBoundActual
import tmp.sheaf.xif.paper.S3051HscalarCaseSplitActual
import tmp.sheaf.xif.paper.S3034PacketScalarBoundActual
import tmp.sheaf.xif.paper.S3025ActualThetaUpperAudit
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import tmp.sheaf.xif.paper.S2807SG3bScalarActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3048MeasureLowerBoundActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S3051HscalarCaseSplitActual
open LeanFormal.IUT.XiFPaper.S3047bActualParameterHscalarAttempt
open LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual
open LeanFormal.IUT.XiFPaper.S3025ActualThetaUpperAudit
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3049S3048ToS3034Actual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-- S3047b hscalar at logQ = 1 from S3048's actual measure lower bound. -/
theorem S3049_hscalar_logQ_one (a b c : Nat) (habc : IsABCTriple a b c) :
    S3047bHscalar C3 a b c := by
  have h := S3048_measureLowerBound C3 a b c habc
  exact S3047b_hscalar_of_measureLowerBound C3 a b c h

/-- S3034Hscalar at logQ = 1 (same S2990DFpd/FFpd parameters). -/
theorem S3049_S3034Hscalar_logQ_one (a b c : Nat) (habc : IsABCTriple a b c) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D 1 a b c := by
  have h := S3049_hscalar_logQ_one
    (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat D) a b c habc
  simpa [S3034Hscalar, S3047bHscalar, S3047bCTheta, S3047bQ,
    S3025MissingThetaUpperScalar] using h

/-- S3025MissingThetaUpperScalar at logQ = 1. -/
theorem S3049_S3025Missing_logQ_one (a b c : Nat) (habc : IsABCTriple a b c) :
    S3025MissingThetaUpperScalar R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D 1 0
      S2990DFpd (S2990FFpd a b c) 0 0 :=
  S3049_S3034Hscalar_logQ_one R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D a b c habc

#check S3049_hscalar_logQ_one
#check S3049_S3034Hscalar_logQ_one
#check S3049_S3025Missing_logQ_one
#print axioms S3049_S3034Hscalar_logQ_one

end LeanFormal.IUT.XiFPaper.S3049S3048ToS3034Actual
end
