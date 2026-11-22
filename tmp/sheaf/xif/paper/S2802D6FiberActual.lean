import Iut.Foundations.Orbicurve

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2802D6FiberActual

universe u

/-- The scheme-representable etale pseudofunctor over an arbitrary scheme X
over F. -/
noncomputable def S2802Fiber (F : Type u) [Field F]
    (X : Iut.SchemeOverField F) : Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F X

#check S2802Fiber
#check Iut.schemeRepresentableEtalePseudofunctor
#check Iut.schemeRepresentableFiberFunctor

end LeanFormal.IUT.XiFPaper.S2802D6FiberActual
end
