import tmp.sheaf.xif.paper.S2541EssSurjAuditActual
import tmp.sheaf.xif.paper.S2519InvFunctorActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option maxHeartbeats 8000000

namespace Probe

-- 1. fiber defeq
example : S2482Orbicurve.stack.fiber = Iut.schemeRepresentableEtalePseudofunctor F S2517S := rfl
example (T : Iut.SchemeOverField F) : (S2517TStack T).fiber = Iut.schemeRepresentableEtalePseudofunctor F T := rfl
-- 2. S2517Point type
#check @S2517Point
example : Pseudofunctor.StrongTrans (Iut.schemeRepresentableEtalePseudofunctor F S2517S) S2482Orbicurve.stack.fiber := S2517Point

variable (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
variable (hrep : S2541Representable X)

noncomputable def bc := X.finiteEtale.baseChange S2482AffineOver S2517Point

example : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F bc.pullbackScheme) X.source.fiber := bc.toSource
example : (X.map) = (X.map : Pseudofunctor.StrongTrans X.source.fiber S2482Orbicurve.stack.fiber) := rfl

noncomputable def S := hrep.choose
example : X.source = S2517TStack S := hrep.choose_spec
lemma fibEq : X.source.fiber = Iut.schemeRepresentableEtalePseudofunctor F S := by
  rw [hrep.choose_spec]; rfl

noncomputable def t' : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F bc.pullbackScheme)
    (Iut.schemeRepresentableEtalePseudofunctor F S) :=
  (fibEq X hrep) ▸ bc.toSource

noncomputable def m' : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F S)
    (Iut.schemeRepresentableEtalePseudofunctor F S2517S) :=
  (fibEq X hrep) ▸ X.map

noncomputable def u : bc.pullbackScheme ⟶ S := S1742HomOfStrongTrans (t' X hrep)
noncomputable def f : S ⟶ S2517S := S1742HomOfStrongTrans (m' X hrep)

end Probe
end
