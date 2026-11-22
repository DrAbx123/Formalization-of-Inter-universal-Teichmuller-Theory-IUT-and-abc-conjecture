import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S2975bA6QPresheafHomSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2975bA6QPresheafHomSheaf
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
namespace LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite

def S3026NonemptyProperty : ObjectProperty (Iut.SchemeOverField S2844D6F6BaseChangeActual.K) :=
  fun X => Nonempty X.left

abbrev S3026NonemptyScheme : Type 1 :=
  S3026NonemptyProperty.FullSubcategory

abbrev S3026NonemptySite :
    GrothendieckTopology S3026NonemptyScheme :=
  S3026NonemptyProperty.ι.inducedTopology
    (Iut.SchemeOverField.etaleTopology S2844D6F6BaseChangeActual.K)

noncomputable def S3026Q : Pseudofunctor
    (LocallyDiscrete S3026NonemptySchemeᵒᵖ) Cat :=
  (S3026NonemptyProperty.ι.op ⋙ S2882A6PFunctor).toPseudofunctor'

def S3026QIsPrestack : Prop :=
  S3026Q.IsPrestack S3026NonemptySite

def S3026QIsStack : Prop :=
  S3026Q.IsStack S3026NonemptySite

theorem S3026_emptyBase_not_obj :
    ¬ Nonempty ((S2975bA6QPresheafHomSheaf.emptyBase :
      Iut.SchemeOverField S2844D6F6BaseChangeActual.K)).left :=
  fun h => h.elim fun x => isEmptyElim x

#check S3026NonemptyProperty
#check S3026NonemptyScheme
#check S3026NonemptySite
#check S3026Q
#check S3026QIsPrestack
#check S3026QIsStack
#check S3026_emptyBase_not_obj

end LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite