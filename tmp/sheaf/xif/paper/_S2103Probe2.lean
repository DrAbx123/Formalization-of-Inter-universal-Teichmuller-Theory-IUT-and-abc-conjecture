import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
variable {S : C} (M N : Sheaf (J.over S) A) (X : Over S)

-- the dense subsite instance
example : (Over.iteratedSliceBackward X).IsDenseSubsite (J.over X.left) ((J.over S).over X) := inferInstance

-- the pushforward we want
#check (Over.iteratedSliceBackward X).sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)

example : Functor.Full ((Over.iteratedSliceBackward X).sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)) := inferInstance
example : Functor.Faithful ((Over.iteratedSliceBackward X).sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)) := inferInstance

-- overPullback and overMapPullback
#check (J.over S).overPullback A X
#check J.overMapPullback A X.hom

-- check definitional equality of functors
example : J.overMapPullback A X.hom =
    ((J.over S).overPullback A X) ⋙ (Over.iteratedSliceBackward X).sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X) := rfl

end Probe
