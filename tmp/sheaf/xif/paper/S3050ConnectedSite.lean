import tmp.sheaf.xif.paper.S3026NonemptyEtaleSite
import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S3037cBottomNotCoveringConcrete
import tmp.sheaf.xif.paper.S3042bUnconditionalQEffectiveDescent
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
namespace LeanFormal.IUT.XiFPaper.S3050ConnectedSite

abbrev K : Type := S2844D6F6BaseChangeActual.K

/-- Connected nonempty schemes over K. -/
def S3050ConnectedProperty : ObjectProperty (Iut.SchemeOverField K) :=
  fun X => Nonempty X.left ∧ ConnectedSpace X.left

abbrev S3050ConnectedScheme : Type 1 :=
  S3050ConnectedProperty.FullSubcategory

abbrev S3050ConnectedSite : GrothendieckTopology S3050ConnectedScheme :=
  S3050ConnectedProperty.ι.inducedTopology
    (Iut.SchemeOverField.etaleTopology K)

abbrev S3050Q : Pseudofunctor
    (LocallyDiscrete S3050ConnectedSchemeᵒᵖ) Cat :=
  (S3050ConnectedProperty.ι.op ⋙ S2882A6PFunctor).toPseudofunctor'

def S3050QIsPrestack : Prop :=
  S3050Q.IsPrestack S3050ConnectedSite

def S3050QIsStack : Prop :=
  S3050Q.IsStack S3050ConnectedSite

/-- The connected-site presheaf-hom sheaf condition. -/
def S3050HomSheafCondition : Prop :=
  ∀ (S : S3050ConnectedScheme) (M N : S3050Q.obj { as := Opposite.op S }),
    Presheaf.IsSheaf (S3050ConnectedSite.over S) (S3050Q.presheafHom M N)

/-- Connectedness excludes the two-component counterexample shape. -/
def S3050DisconnectedObstructionExcluded : Prop :=
  ∀ (U : S3050ConnectedScheme) (A B : Iut.SchemeOverField K),
    Nonempty A.left → Nonempty B.left →
      ¬ Nonempty (U.obj ≅ Over.mk (Limits.coprod.desc A.hom B.hom))

#check S3050ConnectedProperty
#check S3050ConnectedScheme
#check S3050ConnectedSite
#check S3050Q
#check S3050QIsPrestack
#check S3050QIsStack
#check S3050HomSheafCondition
#check S3050DisconnectedObstructionExcluded

end LeanFormal.IUT.XiFPaper.S3050ConnectedSite