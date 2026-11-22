import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
variable {S : C} (M N : Sheaf (J.over S) A) (X : Over S)

example : X.iteratedSliceEquiv.inverse = X.iteratedSliceBackward := rfl

example : X.iteratedSliceEquiv.inverse.IsDenseSubsite (J.over X.left) ((J.over S).over X) := inferInstance

example : Functor.Full (X.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)) := inferInstance
example : Functor.Faithful (X.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)) := inferInstance

end Probe
