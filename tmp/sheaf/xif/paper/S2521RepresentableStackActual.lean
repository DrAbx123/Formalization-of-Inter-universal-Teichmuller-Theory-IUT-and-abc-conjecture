import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed
import tmp.sheaf.n8.closure.DiscreteSheafIsStack

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual

/-- Every representable etale stack over F is an actual stack. -/
theorem S2521RepresentableIsStack (T : Iut.SchemeOverField F) :
    (Iut.schemeRepresentableEtalePseudofunctor F T).IsStack
      (Iut.SchemeOverField.etaleTopology F) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology F)
      (yoneda.obj T) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := F) T)
  change (discretePseudo (C := Iut.SchemeOverField F)
    (yoneda.obj T)).IsStack
      (Iut.SchemeOverField.etaleTopology F)
  exact LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual.DiscreteSheafStack.discretePseudo_isStack
    (P := yoneda.obj T) hP

/-- The base stack of S2482 as an actual etale stack over F. -/
noncomputable def S2517SStack : Iut.EtaleStackOverField F where
  fiber := Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver
  isStack := S2521RepresentableIsStack S2482AffineOver

/-- An arbitrary representable test stack. -/
noncomputable def S2517TStack (T : Iut.SchemeOverField F) :
    Iut.EtaleStackOverField F where
  fiber := Iut.schemeRepresentableEtalePseudofunctor F T
  isStack := S2521RepresentableIsStack T

#check S2521RepresentableIsStack
#check S2517SStack
#check S2517TStack
#print axioms S2517SStack
#print axioms S2517TStack

end LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
end
