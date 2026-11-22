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

#synth Quiver (SingleObj G)
#synth Category (SingleObj G)
#synth Quiver ((SingleObj G)ᵒᵖ)
#synth Category ((SingleObj G)ᵒᵖ)

example (j : (SingleObj G)ᵒᵖ) : j = Opposite.op (SingleObj.star G) := Subsingleton.elim _ _
example (j : SingleObj G) : j = SingleObj.star G := Subsingleton.elim _ _

example (j : (SingleObj G)ᵒᵖ) (f : j ⟶ j) : Opposite.unop j ⟶ Opposite.unop j := f
example (j : (SingleObj G)ᵒᵖ) (f : Opposite.unop j ⟶ Opposite.unop j) : j ⟶ j := f
example (j : (SingleObj G)ᵒᵖ) (f : j ⟶ j) : G := (show Opposite.unop j ⟶ Opposite.unop j from f)
example (j : SingleObj G) (f : j ⟶ j) : G := f
example (j : SingleObj G) (f : G) : j ⟶ j := f

end ProbeS1770
