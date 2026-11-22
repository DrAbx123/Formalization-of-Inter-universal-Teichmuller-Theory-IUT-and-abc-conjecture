import tmp.sheaf.xif.paper.S2508CuspDataUB
import tmp.sheaf.xif.paper.S1913S1726CompactificationActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2873CuspGenericActual

universe u
variable {F : Type u} [Field F]

/-- Generic data for a boundary cusp of an arbitrary hyperbolic orbicurve.
This is exactly the field set of OrbicurveBoundaryCusp; it is recorded
explicitly so that concrete cusp constructions can be shared by an arbitrary
consumer. -/
structure GenericCuspData (X : Iut.HyperbolicOrbicurve F) where
  compactification : Iut.EtaleStackOverField F
  openMap : X.stack.Hom compactification
  openImmersion : Iut.EtaleStackOpenImmersion openMap
  residueScheme : Iut.SchemeOverField F
  point : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F residueScheme)
    compactification.fiber
  isBoundary : forall object :
    X.stack.fiber.obj
      (LocallyDiscrete.mk (Opposite.op residueScheme)),
    IsEmpty
      ((openMap.app
          (LocallyDiscrete.mk (Opposite.op residueScheme))).toFunctor.obj
            object ≅
        Iut.OrbicurveFiniteEtaleCover.pointObject residueScheme point)

/-- Generic cusp constructor: no data is invented, the isBoundary field is
transported verbatim. -/
noncomputable def cuspOfGenericData {X : Iut.HyperbolicOrbicurve F}
    (D : GenericCuspData X) : Iut.OrbicurveBoundaryCusp X where
  compactification := D.compactification
  openMap := D.openMap
  openImmersion := D.openImmersion
  residueScheme := D.residueScheme
  point := D.point
  isBoundary := D.isBoundary

/-- The generic data type is exactly the cusp type up to packaging. -/
theorem nonempty_cusp_iff {X : Iut.HyperbolicOrbicurve F} :
    Nonempty (Iut.OrbicurveBoundaryCusp X) ↔ Nonempty (GenericCuspData X) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨{ compactification := c.compactification,
             openMap := c.openMap,
             openImmersion := c.openImmersion,
             residueScheme := c.residueScheme,
             point := c.point,
             isBoundary := c.isBoundary }⟩
  · rintro ⟨D⟩
    exact ⟨cuspOfGenericData D⟩

/-! S1913 supplies a reusable cusp constructor only for S1726Orbicurve. -/
#check S1913S1726CompactificationActual.S1913AffineCompactification.S1913BoundaryCusp

#check GenericCuspData
#check cuspOfGenericData
#check nonempty_cusp_iff
#print axioms cuspOfGenericData
#print axioms nonempty_cusp_iff

end LeanFormal.IUT.XiFPaper.S2873CuspGenericActual
end