import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2500CuspDataActual

/-- The explicit data needed for a boundary cusp on `S2495cK`: a
compactification stack, an open immersion from `S2495cK`, a residue scheme,
a point of the compactification at that residue, and the boundary condition. -/
structure S2500CuspData where
  compactification : Iut.EtaleStackOverField S2490A.K
  openMap : S2495cK.stack.Hom compactification
  openImmersion : Iut.EtaleStackOpenImmersion openMap
  residueScheme : Iut.SchemeOverField S2490A.K
  point : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor S2490A.K residueScheme)
    compactification.fiber
  isBoundary : ∀ object :
    S2495cK.stack.fiber.obj
      (LocallyDiscrete.mk (Opposite.op residueScheme)),
    IsEmpty
      ((openMap.app
          (LocallyDiscrete.mk (Opposite.op residueScheme))).toFunctor.obj
            object ≅
        Iut.OrbicurveFiniteEtaleCover.pointObject residueScheme point)

noncomputable def S2500CuspOfData (D : S2500CuspData) :
    Iut.OrbicurveBoundaryCusp S2495cK where
  compactification := D.compactification
  openMap := D.openMap
  openImmersion := D.openImmersion
  residueScheme := D.residueScheme
  point := D.point
  isBoundary := D.isBoundary

theorem S2500_cusp_nonempty_iff :
    Nonempty (Iut.OrbicurveBoundaryCusp S2495cK) ↔ Nonempty S2500CuspData := by
  constructor
  · rintro ⟨c⟩
    exact ⟨{ compactification := c.compactification,
             openMap := c.openMap,
             openImmersion := c.openImmersion,
             residueScheme := c.residueScheme,
             point := c.point,
             isBoundary := c.isBoundary }⟩
  · rintro ⟨D⟩
    exact ⟨S2500CuspOfData D⟩

#print axioms S2500_cusp_nonempty_iff
#print axioms S2500CuspOfData

end LeanFormal.IUT.XiFPaper.S2500CuspDataActual
end