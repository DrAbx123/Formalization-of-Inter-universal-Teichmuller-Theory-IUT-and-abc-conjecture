import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe9

universe v u

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type v) (Y : C)

example (a b : (discretePseudo P).obj (LocallyDiscrete.mk (Opposite.op Y))) :
    Subsingleton (a ⟶ b) := inferInstance

example (a b : (discretePseudo P).obj (LocallyDiscrete.mk (Opposite.op Y))) :
    ∀ (x y : a ⟶ b), x = y := fun x y => Subsingleton.elim x y

end S1419Probe9

end
