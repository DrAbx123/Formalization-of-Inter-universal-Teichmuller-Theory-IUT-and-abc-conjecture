import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]

#print CategoryTheory.GrothendieckTopology.pseudofunctorOver

#check @CategoryTheory.GrothendieckTopology.pseudofunctorOver_obj
#check @CategoryTheory.GrothendieckTopology.pseudofunctorOver_map
#check @CategoryTheory.GrothendieckTopology.pseudofunctorOver_mapComp

end Probe
