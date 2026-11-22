import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
open WeierstrassCurve
open scoped WeierstrassCurve
variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
#check (W.baseChange F).Point
#check (W.baseChange F).toAffine.Point
#check ((W⁄F) : WeierstrassCurve.Affine F).Point
#check WeierstrassCurve.Affine.Point (W.baseChange F)
#check fun (P : (W.baseChange F).Point) => P
#check fun (P : (W.baseChange F).toAffine.Point) => P
#check @WeierstrassCurve.Affine.Point.baseChange
