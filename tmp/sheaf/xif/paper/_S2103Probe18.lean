import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.SheafHom

noncomputable section
open CategoryTheory Opposite

namespace Probe

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (J.pseudofunctorOver A).mapComp (g.op.toLoc) (f.op.toLoc) =
      Cat.Hom.isoMk (J.overMapPullbackComp A f g).symm := by
  simp [GrothendieckTopology.pseudofunctorOver]

end Probe
