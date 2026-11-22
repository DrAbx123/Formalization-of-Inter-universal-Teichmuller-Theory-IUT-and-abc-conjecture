import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
variable {S : C} (M N : Sheaf (J.over S) A)

abbrev slicePush (X : Over S) : Sheaf ((J.over S).over X) A ⥤ Sheaf (J.over X.left) A :=
  X.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)

instance (X : Over S) : (slicePush (J := J) (A := A) X).Full := inferInstance
instance (X : Over S) : (slicePush (J := J) (A := A) X).Faithful := inferInstance

set_option maxHeartbeats 800000 in
lemma key (X₁ X₂ : (Over S)ᵒᵖ) (f : X₁ ⟶ X₂)
    (φ : (CategoryTheory.sheafHom' (J := J.over S) M N).obj X₁) :
    (slicePush (J := J) (A := A) X₂.unop).map (((J.over S).overMapPullback A f.unop).map φ) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := J.pseudofunctorOver A)
        ((slicePush (J := J) (A := A) X₁.unop).map φ) f.unop.left X₂.unop.hom X₂.unop.hom := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  apply Sheaf.hom_ext
  ext Z
  trace_state
  sorry

end Probe
