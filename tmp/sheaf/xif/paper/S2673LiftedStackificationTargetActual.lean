import tmp.sheaf.xif.paper.S2671D9StackificationLayerActual
import Mathlib.CategoryTheory.Sites.Descent.IsStack

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2673LiftedStackificationTargetActual

universe u
variable {F : Type u} [Field F]

/-- New target after the universe correction: a `Cat.{u+1,u+1}`-valued etale stack
on the scheme site.  This is the stack-side replacement for the impossible
`Cat.{0,u}`-valued stackification; a fully faithful comparison is a separate
obligation and is not encoded here. -/
def S2673LiftedStackificationTarget : Prop :=
  ∃ G : Pseudofunctor (LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) Cat.{u+1, u+1},
    G.IsStack (Iut.SchemeOverField.etaleTopology F)

#check S2673LiftedStackificationTarget

end LeanFormal.IUT.XiFPaper.S2673LiftedStackificationTargetActual
end