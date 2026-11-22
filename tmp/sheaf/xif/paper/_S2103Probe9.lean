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

set_option pp.all true in
example : True := by
  have h : CategoryTheory.sheafHom' (J := J.over S) M N ⟶ (J.pseudofunctorOver A).presheafHom M N :=
  { app X := ↾fun φ => (slicePush (J := J) (A := A) X.unop).map φ
    naturality X₁ X₂ f := by
      ext φ
      trace_state
      sorry }
  trivial

end Probe
