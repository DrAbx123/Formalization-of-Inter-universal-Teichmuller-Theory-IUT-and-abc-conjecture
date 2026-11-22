import tmp.sheaf.xif.paper.S3088FamilyConstructionActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3088FamilyConstructionActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

/-- The corrected selected-places type. -/
abbrev S3089Selected : Type :=
  Selected (S2696SelectionTwo fiveLabel)

/-- The corrected source datum over the S2696 two-place selection. -/
noncomputable abbrev S3089Source : SourceDefinition31Data.{0} fiveLabel :=
  S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- Nonempty corrected selected places, chosen from the actual bad-place
selection through its place bijection (no instance registration). -/
noncomputable def S3089SelectedNonempty : Nonempty S3089Selected :=
  let P := S2696SelectionTwo fiveLabel
  let w := P.V_mod_bad_nonempty.choose
  ⟨P.V_mod_bijection (NumberFieldPlace.finite w)⟩

/-- The generic shear family at the corrected selected places. -/
noncomputable def S3089Family
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} fiveLabel S3089Selected :=
  @S3088Family S3089Selected S3089SelectedNonempty
    (S3089Source R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic

/-- The corrected OriginalInput over V = Selected places. -/
noncomputable def S3089CorrectedOriginalInput
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OriginalInput.{0, 0, 0, 0, 0} fiveLabel S3089Selected where
  initial := S3089Source R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat
  family := S3089Family R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat
  index_equiv := by exact Equiv.refl _
  arithmetic_alignment := by
    intro i
    rfl

/-- The corrected input's selectedPlaces is exactly the Selected type. -/
theorem S3089_selected_eq :
    (S3089CorrectedOriginalInput R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.selectedPlaces =
      S3089Selected := rfl

#check S3089CorrectedOriginalInput
#check S3089_selected_eq
#print axioms S3089CorrectedOriginalInput

end LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual
end