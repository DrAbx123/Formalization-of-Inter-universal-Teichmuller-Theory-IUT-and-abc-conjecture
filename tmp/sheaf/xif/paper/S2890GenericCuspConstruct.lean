import tmp.sheaf.xif.paper.S2885EpsilonInputActual
import tmp.sheaf.xif.paper.S2880CorrectedA6CoreNontrivialActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import tmp.sheaf.xif.paper.S2851A6D6GeometryActual

noncomputable section
open LeanFormal.IUT
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2890GenericCuspConstruct

universe u
variable {F : Type u} [Field F]

/-- Package an existing actual cusp into GenericCuspData. This is the only
unconditional constructor available without new compactification data. -/
noncomputable def genericCuspDataOfCusp
    {X : Iut.HyperbolicOrbicurve F} (c : Iut.OrbicurveBoundaryCusp X) :
    LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.GenericCuspData X :=
  { compactification := c.compactification
    openMap := c.openMap
    openImmersion := c.openImmersion
    residueScheme := c.residueScheme
    point := c.point
    isBoundary := c.isBoundary }

/-- The packaging round-trips to the original cusp. -/
theorem cuspOf_genericCuspDataOfCusp
    {X : Iut.HyperbolicOrbicurve F} (c : Iut.OrbicurveBoundaryCusp X) :
    LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.cuspOfGenericData
      (genericCuspDataOfCusp c) = c := by
  cases c
  rfl

/-- For A6, the epsilon field of S2880Inputs directly yields GenericCuspData. -/
noncomputable def S2890A6CuspData
    {signAction : Iut.OrbicurveSignAction
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve}
    (I : LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual.S2880Inputs signAction) :
    LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.GenericCuspData I.cK :=
  genericCuspDataOfCusp I.epsilon

#check genericCuspDataOfCusp
#check cuspOf_genericCuspDataOfCusp
#check S2890A6CuspData
#print axioms genericCuspDataOfCusp
#print axioms cuspOf_genericCuspDataOfCusp

end LeanFormal.IUT.XiFPaper.S2890GenericCuspConstruct
end