import tmp.sheaf.xif.paper.S3043LocalHaarVolumeSignActual
import tmp.sheaf.xif.paper.S2957IndependentCThetaUpperActual
import tmp.sheaf.xif.paper.S2990ActualDFpdActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S2957IndependentCThetaUpperActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3047bActualParameterHscalarAttempt

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- CThetaPaper with the actual S2990 different norm and support norm
(paper source parameters, NOT the S2959 exp-reversed parameter). -/
noncomputable def S3047bCTheta (a b c : Nat) : Real :=
  CThetaPaper fiveLabel 1 0 S2990DFpd (S2990FFpd a b c) 0 0

noncomputable def S3047bQ : Real := paperQAbsLog fiveLabel 1

/-- The paper hscalar target with actual different norm. -/
def S3047bHscalar (a b c : Nat) : Prop :=
  -actualC3LogShellTensorLogVolume C3 <=
    S3047bCTheta a b c * S3047bQ

/-- The exact missing measure lower bound object:
`V >= -C*Q` where `C = CThetaPaper` and `Q = paperQAbsLog`. -/
def S3047bMissingMeasureLowerBound (a b c : Nat) : Prop :=
  -S3047bCTheta a b c * S3047bQ <=
    actualC3LogShellTensorLogVolume C3

theorem S3047b_hscalar_iff_measureLowerBound (a b c : Nat) :
    S3047bHscalar C3 a b c ↔ S3047bMissingMeasureLowerBound C3 a b c := by
  unfold S3047bHscalar S3047bMissingMeasureLowerBound
  constructor <;> intro h <;> linarith

/-- Conditional hscalar from the exact measure lower bound. -/
theorem S3047b_hscalar_of_measureLowerBound
    (a b c : Nat) (h : S3047bMissingMeasureLowerBound C3 a b c) :
    S3047bHscalar C3 a b c :=
  (S3047b_hscalar_iff_measureLowerBound C3 a b c).mpr h

#check S3047bCTheta
#check S3047bQ
#check S3047bHscalar
#check S3047bMissingMeasureLowerBound
#check S3047b_hscalar_iff_measureLowerBound
#check S3047b_hscalar_of_measureLowerBound
#print axioms S3047b_hscalar_iff_measureLowerBound

end LeanFormal.IUT.XiFPaper.S3047bActualParameterHscalarAttempt
end
