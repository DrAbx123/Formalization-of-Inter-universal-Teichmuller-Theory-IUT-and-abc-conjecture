import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
variable {S : C} (M N : Sheaf (J.over S) A) (X : Over S)

example : (J.overMapPullback A X.hom).obj M =
    (X.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)).obj
      (((J.over S).overPullback A X).obj M) := rfl

-- objects of presheafHom
example : ((J.pseudofunctorOver A).presheafHom M N).obj (op X) =
    (((J.over S).overPullback A X).obj M ⟶ ((J.over S).overPullback A X).obj N) := rfl
-- hmm: this won't be rfl because the Hom is taken in the sheaf category after pushforward.

end Probe
