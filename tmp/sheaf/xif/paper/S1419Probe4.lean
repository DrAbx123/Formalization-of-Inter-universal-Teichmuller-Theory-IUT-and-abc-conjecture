import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe4

universe v u

variable {C : Type u} [Category.{v} C] {X : C}

example (P : Cᵒᵖ ⥤ Type v) (Z : C) (g : Z ⟶ X) (a : (discretePseudo P).obj (LocallyDiscrete.mk (Opposite.op X))) :
    ((discretePseudo P).map (Quiver.Hom.toLoc g.op)).toFunctor.obj a =
      Discrete.mk (P.map g.op a.as) := rfl

end S1419Probe4

end
