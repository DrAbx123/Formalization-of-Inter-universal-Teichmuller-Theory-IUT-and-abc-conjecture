import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

namespace Probe

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

example (P : W.Point) : (W⁄W.FunctionField).Point :=
  Point.baseChange (W' := W) F W.FunctionField P

#check Point.baseChange
#check Point.map_baseChange
#check WeierstrassCurve.Affine.Point.map
#check WeierstrassCurve.baseChange_nonsingular

end Probe
