import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]

example {X Y : C} (f : X ⟶ Y) :
    (J.pseudofunctorOver A).map (f.op.toLoc) = (J.overMapPullback A f).toCatHom := by
  simp [GrothendieckTopology.pseudofunctorOver]

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (J.pseudofunctorOver A).mapComp (f.op.toLoc) (g.op.toLoc) =
      Cat.Hom.isoMk (J.overMapPullbackComp A f g).symm := by
  simp [GrothendieckTopology.pseudofunctorOver]

end Probe
