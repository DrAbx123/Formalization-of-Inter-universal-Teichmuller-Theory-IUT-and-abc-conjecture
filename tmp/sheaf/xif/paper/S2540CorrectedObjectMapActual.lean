import tmp.sheaf.xif.paper.S2538AffineCoverEquivActual
import tmp.sheaf.xif.paper.S2519InvFunctorActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual

namespace LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual

noncomputable def S2540ObjectMap
    (A : CommAlgCat.FiniteEtale S2482CoordinateRing) :
    Iut.OrbicurveFiniteEtaleCover S2482Orbicurve :=
  S2519InvFunctor.obj
    (S2538AffineCoverEquiv.inverse.obj (Opposite.op A))

noncomputable def S2540Functor :
    (CommAlgCat.FiniteEtale S2482CoordinateRing)ᵒᵖ ⥤
      Iut.OrbicurveFiniteEtaleCover S2482Orbicurve :=
  S2538AffineCoverEquiv.inverse ⋙ S2519InvFunctor

#check S2540ObjectMap
#check S2540Functor
#print axioms S2540Functor
end LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
end