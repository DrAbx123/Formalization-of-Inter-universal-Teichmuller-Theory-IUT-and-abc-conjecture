import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

/-! # S1353: D6 orbicurve actual — exact first field

Read: `Example36OrbicurveFeasibility`, `CurveEtaleFundamentalGroup`,
`S1331OrbicurveClauseAudit` (S1348 produced no artifact).

The actual S1280/Example36 data supply:
* the actual punctured elliptic curve `concretePuncturedCurve` (y^2 = x^3 + 1)
  / S1280 Gaussian curve;
* the actual curve-point carrier and its -1 involution;
* the actual geometric fiber-functor automorphism group of the
  y^2 = x^3 - x punctured curve.

They do NOT supply the D6 orbicurve clause fields:
`cover`, `structureGroup`, `coverToPunctured`, surjectivity, the
`SourceExactSequenceClause`, and `cuspCount`.  The exact missing object is
`MissingD6GeometricRealization F` (nondegenerate etale stack fiber + effective
descent + surjective curve-point realization); no inhabitant exists in the
tree.  A trivial cover=curve / structureGroup=ZMod 2 or a terminal/PUnit fiber
would not be the source orbicurve and is not used.

This file records the exact first field; it does not construct D6. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1353D6OrbicurveActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

#check MissingD6GeometricRealization
#check MissingD6GeometricRealization.curve
#check MissingD6GeometricRealization.fiber
#check MissingD6GeometricRealization.isStack
#check MissingD6GeometricRealization.nondegenerate
#check MissingD6GeometricRealization.curvePointRealization
#check concretePuncturedCurve
#check concreteEllipticCurve
#check oncePuncturedSignature
#check OncePuncturedGeometricCarrier

end LeanFormal.IUT.XiFPaper.S1353D6OrbicurveActual
end
