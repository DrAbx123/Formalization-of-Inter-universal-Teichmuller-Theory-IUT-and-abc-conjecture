import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

noncomputable section
open CategoryTheory Opposite

namespace LeanFormal.IUT.XiFPaper.S2103D9PrestackActual

universe v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

abbrev slicePush {S : C} (X : Over S) : Sheaf ((J.over S).over X) A ⥤ Sheaf (J.over X.left) A :=
  X.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)

lemma slicePush_full {S : C} (X : Over S) : (slicePush (J := J) (A := A) X).Full :=
  inferInstance

lemma slicePush_faithful {S : C} (X : Over S) : (slicePush (J := J) (A := A) X).Faithful :=
  inferInstance

/-- the key pointwise identification of the objects. -/
lemma presheafHom_obj_eq {S : C} (M : Sheaf (J.over S) A) (X : Over S) :
    (J.overMapPullback A X.hom).obj M =
      (slicePush (J := J) (A := A) X).obj (((J.over S).overPullback A X).obj M) := rfl

def sliceComparison {S : C} (M N : Sheaf (J.over S) A) (X : Over S) :
    (CategoryTheory.sheafHom' (J := J.over S) M N).obj (op X) →
      ((J.pseudofunctorOver A).presheafHom M N).obj (op X) :=
  fun φ => (slicePush (J := J) (A := A) X).map φ

lemma sliceComparison_bijective {S : C} (M N : Sheaf (J.over S) A) (X : Over S) :
    Function.Bijective (sliceComparison (J := J) (A := A) M N X) := by
  haveI := slicePush_full (J := J) (A := A) X
  haveI := slicePush_faithful (J := J) (A := A) X
  constructor
  · intro a b h
    exact Functor.Faithful.map_injective (F := slicePush (J := J) (A := A) X) h
  · intro b
    exact Functor.Full.map_surjective (F := slicePush (J := J) (A := A) X) b

end LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
