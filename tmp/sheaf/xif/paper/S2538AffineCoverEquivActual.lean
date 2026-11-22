import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual

noncomputable def S2538AffineCoverEquiv :
    FiniteEtaleCover S2482AffineScheme ≌
      (CommAlgCat.FiniteEtale S2482CoordinateRing)ᵒᵖ :=
  affineFiniteEtaleEquivalenceCoverFirst (R := S2482CoordinateRing)

#check S2538AffineCoverEquiv
#print axioms S2538AffineCoverEquiv
end LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
end