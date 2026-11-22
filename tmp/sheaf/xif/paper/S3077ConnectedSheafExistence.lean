import tmp.sheaf.xif.paper.S3057ConnectedHomSheaf
import tmp.sheaf.xif.paper.S3042bUnconditionalQEffectiveDescent
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3057ConnectedHomSheaf
namespace LeanFormal.IUT.XiFPaper.S3077ConnectedSheafExistence

abbrev K : Type := S3050ConnectedSite.K

/-- The connected-site hom sheaf target. -/
def S3077ConnectedHomSheaf : Prop :=
  S3050HomSheafCondition

/-- The exact missing graph-connectivity input: any covering sieve has an
index-graph connected by common refinements. -/
def S3077CoverIndexGraphConnected : Prop :=
  ∀ (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T),
    R ∈ S3050ConnectedSite.over S T →
      ∀ (i j : R.arrows.category), ∃ (Z : Over T)
        (g₁ : Z ⟶ i.obj) (g₂ : Z ⟶ j.obj), True

def S3077MissingSheafExistence : Prop :=
  S3077CoverIndexGraphConnected → S3077ConnectedHomSheaf

#check S3077ConnectedHomSheaf
#check S3077CoverIndexGraphConnected
#check S3077MissingSheafExistence
#check S3057_homForm_separated
open LeanFormal.IUT.XiFPaper.S3042bUnconditionalQEffectiveDescent
#check S3042b_QEffectiveDescent

end LeanFormal.IUT.XiFPaper.S3077ConnectedSheafExistence