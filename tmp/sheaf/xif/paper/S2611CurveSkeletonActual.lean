import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.NumberTheory.NumberField.Basic

noncomputable section
open AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2611CurveSkeletonActual

universe u

/-- Concrete skeleton data for the IUT IV §2 proper smooth curve.
No inhabitant is constructed in this file; the fields use actual Mathlib
`Scheme`, `IsProper`, `Smooth`, `GeometricallyConnected`, and
`SmoothOfRelativeDimension` classes. -/
structure IUTIVCurveSkeleton where
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  X : Scheme.{u}
  f : X ⟶ Spec (CommRingCat.of F)
  [proper : IsProper f]
  [smooth : Smooth f]
  [geomConn : GeometricallyConnected f]
  [relDim : SmoothOfRelativeDimension 1 f]

#check IUTIVCurveSkeleton

end LeanFormal.IUT.XiFPaper.S2611CurveSkeletonActual
end
