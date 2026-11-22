import tmp.sheaf.xif.paper.S2103D9PrestackActual

noncomputable section
open CategoryTheory Opposite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2432PrestackCloseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual

universe v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

theorem test_slicePushNaturality {S : C} (M N : Sheaf (J.over S) A) :
    SlicePushNaturality (J := J) (A := A) M N := by
  intro X₁ X₂ f
  ext φ
  change (slicePush (J := J) (A := A) X₂.unop).map
      (((J.over S).overMapPullback A f.unop).map φ) =
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := J.pseudofunctorOver A)
      ((slicePush (J := J) (A := A) X₁.unop).map φ) f.unop.left X₂.unop.hom X₂.unop.hom)
  trace_state
  sorry

end LeanFormal.IUT.XiFPaper.S2432PrestackCloseActual
