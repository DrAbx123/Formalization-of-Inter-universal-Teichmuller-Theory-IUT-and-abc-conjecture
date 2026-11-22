import tmp.sheaf.xif.paper.S2873CuspGenericActual
import tmp.sheaf.xif.paper.S2508CuspDataUB
import tmp.sheaf.xif.paper.S1913S1726CompactificationActual
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2873BoundaryCuspAudit

/-!
Field-by-field reuse audit for Iut.OrbicurveBoundaryCusp:

1. compactification:
   - S2508 S2508Compactification (only S2495cK),
   - S1913 S1913CompactificationStack (S1726Orbicurve),
   - generic: representable etale stack of any scheme over F, with S2199 IsStack.
2. openMap:
   - S2508 S2508StackOpenMap,
   - S1913 S1913StackOpenMap,
   - generic: S1742StrongTransOfHom.
3. openImmersion:
   - S2508/S1913 take EtaleStackOpenImmersion as explicit input; no generic
     construction is present in the tree.
4. residueScheme:
   - S2508 S2508ResidueScheme = Spec UB,
   - S1913 S1726Base,
   - generic: Over.mk (identity (Spec F)).
5. point:
   - S2508 S2508CuspDatum.point (explicit point at infinity input),
   - S1913 S1913BoundaryPoint,
   - generic: no Proj point API; explicit gap.
6. isBoundary:
   - S2508 derived from separation in the datum,
   - S1913 S1913Boundary_isBoundary,
   - generic: requires separation of the point from the open image.
-/

#check Iut.OrbicurveBoundaryCusp
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508Compactification
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508StackOpenMap
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508ResidueScheme
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508CuspDatum
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508CuspDatum.stackOpenImmersion
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508CuspDatum.separation
#check LeanFormal.IUT.XiFPaper.S2508CuspDataUB.S2508CuspDatum.boundaryCusp
#check LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual.S1913AffineCompactification
#check LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual.S1913AffineCompactification.S1913StackOpenMap
#check LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual.S1913AffineCompactification.S1913BoundaryPoint
#check LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual.S1913AffineCompactification.S1913Boundary_isBoundary
#check LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual.S1913AffineCompactification.S1913BoundaryCusp

/-- Generic cusp packaging from exact data (no field invented). -/
noncomputable def S2873CuspOfData {F : Type} [Field F]
    {X : Iut.HyperbolicOrbicurve F}
    (D : LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.GenericCuspData X) :
    Iut.OrbicurveBoundaryCusp X :=
  LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.cuspOfGenericData D

#check S2873CuspOfData
#print axioms S2873CuspOfData

end LeanFormal.IUT.XiFPaper.S2873BoundaryCuspAudit
end