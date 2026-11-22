import tmp.sheaf.xif.paper.S3089CorrectedOriginalInputActual
import tmp.sheaf.xif.paper.S3094ActualQFamilyAttempt
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual
open LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3095ActualQOriginalInputAttempt

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

local instance s3095Nonempty : Nonempty S3089Selected := S3089SelectedNonempty

noncomputable def S3095Family
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))] :
    SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} fiveLabel S3089Selected :=
  S3094Family (V := S3089Selected) T

noncomputable def S3095OriginalInput
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (hT : T.arithmetic =
      (S3089Source R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic) :
    OriginalInput.{0, 0, 0, 0, 0} fiveLabel S3089Selected where
  initial := S3089Source R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
  family := S3095Family T
  index_equiv := Equiv.refl _
  arithmetic_alignment := by
    intro i
    exact hT

/-- No-Fintype local q equality: the constructed family's q is exactly the
actual weighted native q product. -/
theorem S3095_local_q_eq :
    ((S3095OriginalInput R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT).family.theater
      ((S3095OriginalInput R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T hT).indexOf 1 0)).thetaPacket.q =
    S3094WeightedQProduct (T := T) := by
  rfl

#check S3095Family
#check S3095OriginalInput
#check S3095_local_q_eq
#print axioms S3095OriginalInput
#print axioms S3095_local_q_eq

end LeanFormal.IUT.XiFPaper.S3095ActualQOriginalInputAttempt
end
