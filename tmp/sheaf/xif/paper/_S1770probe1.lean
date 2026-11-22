import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace ProbeS1770
universe u

variable {K : Type u} [Field K]
variable (G : Type u) [Group G] [Finite G]

#check @Opposite.op
#check @Quiver.Hom.op

-- how to write op
example (star : SingleObj G) : Opposite.op star = Opposite.op star := rfl

-- hom type of op star
example (j : (SingleObj G)ᵒᵖ) (f : j ⟶ j) : G := f
example (j : (SingleObj G)ᵒᵖ) (f : G) : j ⟶ j := f

-- action via F.map
example (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) (g : G) :
    F.obj (Opposite.op (SingleObj.star G)) ⟶ F.obj (Opposite.op (SingleObj.star G)) := F.map g

end ProbeS1770
