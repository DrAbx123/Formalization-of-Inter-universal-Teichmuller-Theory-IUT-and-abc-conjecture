import tmp.sheaf.xif.paper.S3095ActualQOriginalInputAttempt
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.S3089CorrectedOriginalInputActual
import tmp.sheaf.xif.paper.S3094ActualQFamilyAttempt
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3095ActualQOriginalInputAttempt
open LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual
open LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3102CorrectedC3Actual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (hT : T.arithmetic =
  (S3089Source R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic)

/-- Corrected C3 over the selected places, using the generic actualSignedC3. -/
noncomputable abbrev S3102C3
    (D : SourcePilotRegionDonors (l := fiveLabel) (V := S3089Selected)
      (S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT)) :
    SourcePilotRegionData (l := fiveLabel) (V := S3089Selected)
      (S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT) :=
  actualSignedC3 (l := fiveLabel) (V := S3089Selected) (I := S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT) D

/-- Base-field alignment: corrected C3 input arithmetic is native T arithmetic. -/
theorem S3102_base_field_eq :
    (S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT).initial.arithmetic = T.arithmetic := by
  rw [hT]
  rfl

/-- Exact index target: corrected C3 tensor indices match the native bad family. -/
def S3102IndexTarget
    (D : SourcePilotRegionDonors (l := fiveLabel) (V := S3089Selected) (S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT)) : Prop :=
  Nonempty
    ((S3102C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat T hT D).tensorIndex ≃
      Bad (nativePlaceSelection T))

/-- Exact theta-value target: corrected C3 theta packet q matches the native
weighted q product. -/
def S3102ThetaValueTarget
    (D : SourcePilotRegionDonors (l := fiveLabel) (V := S3089Selected) (S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT)) : Prop :=
  (S3102C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat T hT D).thetaPacket.q =
    S3094WeightedQProduct (T := T)

#check (S3095OriginalInput R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT)
#check S3102C3
#check S3102_base_field_eq
#check S3102IndexTarget
#check S3102ThetaValueTarget

end LeanFormal.IUT.XiFPaper.S3102CorrectedC3Actual
end