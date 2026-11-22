import tmp.sheaf.xif.paper.S2543CorrectedQuotMapActual
import tmp.sheaf.xif.paper.S2540CorrectedObjectMapActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2544D2SchemeMapActual

/-- D2: extract the affine scheme map underlying a cover map between two
inverse objects. -/
noncomputable def S2544AffineSchemeMap
    {A B : CommAlgCat.FiniteEtale S2482CoordinateRing}
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    S2517CScheme (S2538AffineCoverEquiv.inverse.obj (Opposite.op B)) ⟶
      S2517CScheme (S2538AffineCoverEquiv.inverse.obj (Opposite.op A)) :=
  S1742HomOfStrongTrans h0.map

#check S2544AffineSchemeMap
#print axioms S2544AffineSchemeMap

end LeanFormal.IUT.XiFPaper.S2544D2SchemeMapActual
end
