import tmp.sheaf.xif.paper.S2443OverMapCompatActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2444OverMapCompatIsoActual

universe v u v' u'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]
variable {X : C} {f g : Over X} (p : f ⟶ g)

/-- The exact missing functor iso type.  No inhabitant is asserted. -/
abbrev S2444OverMapCompatIsoType : Type (max u v u' v') :=
  (slicePush (J := J) (A := A) g) ⋙ (J.overMapPullback A (Over.Hom.left p)) ≅
    ((J.over X).overMapPullback A p) ⋙ (slicePush (J := J) (A := A) f)

#check S2444OverMapCompatIsoType
#check Over.iteratedSliceEquivOverMapIso
#check GrothendieckTopology.overMapPullbackComp
#check Functor.sheafPushforwardContinuousIso

end LeanFormal.IUT.XiFPaper.S2444OverMapCompatIsoActual

end
