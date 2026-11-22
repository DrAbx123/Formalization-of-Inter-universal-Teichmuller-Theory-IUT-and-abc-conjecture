import tmp.sheaf.xif.paper.S2517RepresentableFiniteEtaleActual
import tmp.sheaf.xif.paper.S2521RepresentableStackActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517StackHomActual

/-- The representable cover map as a morphism of actual stacks. -/
noncomputable def S2517StackHom (C : FiniteEtaleCover S2482AffineScheme) :
    Iut.EtaleStackOverField.Hom
      (S2517TStack (S2517CScheme C)) S2517SStack :=
  S1742StrongTransOfHom (F := F) (S2517OverMap C)

/-- The scheme-valued point as a morphism of actual stacks. -/
noncomputable def S2517Point (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    Iut.EtaleStackOverField.Hom (S2517TStack T) S2517SStack :=
  q

#check S2517StackHom
#check S2517Point

end LeanFormal.IUT.XiFPaper.S2517StackHomActual
end
