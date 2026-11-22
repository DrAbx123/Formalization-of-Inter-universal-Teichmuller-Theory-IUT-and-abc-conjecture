import tmp.sheaf.xif.paper.S3026NonemptyEtaleSite
import tmp.sheaf.xif.paper.S2899A6QPrestackActual
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S2899A6QPrestackActual
namespace LeanFormal.IUT.XiFPaper.S3031NonemptyQIsPrestack

/-- The nonempty-site prestack target for the restricted Q. -/
def S3031QIsPrestack : Prop :=
  S3026Q.IsPrestack S3026NonemptySite

/-- The exact sheaf condition still needed on the nonempty site. -/
def S3031NonemptyHomSheafCondition : Prop :=
  ∀ (S : S3026NonemptyScheme) (M N : S3026Q.obj { as := Opposite.op S }),
    Presheaf.IsSheaf (S3026NonemptySite.over S) (S3026Q.presheafHom M N)

/-- Empty base is excluded from the nonempty site. -/
theorem S3031_emptyBase_excluded :
    ¬ Nonempty ((S2975bA6QPresheafHomSheaf.emptyBase :
      Iut.SchemeOverField S2844D6F6BaseChangeActual.K)).left :=
  S3026_emptyBase_not_obj

#check S3031QIsPrestack
#check S3031NonemptyHomSheafCondition
/-- Recorded gap: the nonempty-site prestack is exactly the open target. -/
def S3031_gap : Prop := S3031QIsPrestack

theorem S3031_gap_iff : S3031_gap ↔ S3031QIsPrestack := Iff.rfl

#check S3031_gap
#check S3031_gap_iff
#check S3031_emptyBase_excluded

end LeanFormal.IUT.XiFPaper.S3031NonemptyQIsPrestack