import tmp.sheaf.xif.paper.S2518InvCoverMapActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517InvFunctorPartialActual

/-- Object map of the inverse functor. -/
noncomputable def S2517InvFunctorObj (C : FiniteEtaleCover S2482AffineScheme) :
    Iut.OrbicurveFiniteEtaleCover S2482Orbicurve :=
  S2517InvObj C

/-- Raw map on homs, landed in the 2-isomorphism quotient. -/
noncomputable def S2517InvFunctorMap {C D : FiniteEtaleCover S2482AffineScheme}
    (f : C ⟶ D) :
    S1728CoverMapClass (A := S2517InvFunctorObj C)
      (B := S2517InvFunctorObj D) :=
  Quot.mk _ (S2518InvCoverMap f)

#check S2517InvFunctorObj
#check S2517InvFunctorMap

end LeanFormal.IUT.XiFPaper.S2517InvFunctorPartialActual
end
