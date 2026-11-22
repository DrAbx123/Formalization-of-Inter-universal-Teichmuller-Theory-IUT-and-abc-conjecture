import tmp.sheaf.xif.paper.S2498InvariantActual
import tmp.sheaf.xif.paper.S2470SignActionActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
open LeanFormal.IUT.XiFPaper.S2498InvariantActual
open LeanFormal.IUT.XiFPaper.S2470SignActionActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2499QuotientActualAdapted

noncomputable def S2499Quotient :
    Iut.OrbicurveSignInvariantMorphism S2470SignAction S2495cF where
  map := S2496Map
  invariant := S2498Invariant
  cocycle := by
    ext a
    apply CategoryTheory.Cat.Hom₂.ext
    intro X
    apply Subsingleton.elim

#print axioms S2499Quotient

end LeanFormal.IUT.XiFPaper.S2499QuotientActualAdapted
end