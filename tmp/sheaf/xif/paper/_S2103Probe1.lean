import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
variable {S : C} (M N : Sheaf (J.over S) A)

#check CategoryTheory.sheafHom' (J := J.over S) M N
#check @CategoryTheory.sheafHom' (Over S) _ (J.over S) A _ M N

example : Nonempty ((J.pseudofunctorOver A).presheafHom M N ≅ CategoryTheory.sheafHom' (J := J.over S) M N) := inferInstance

end Probe
