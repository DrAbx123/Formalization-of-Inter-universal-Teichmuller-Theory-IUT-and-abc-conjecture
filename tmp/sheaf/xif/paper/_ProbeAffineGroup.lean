import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
open WeierstrassCurve
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
example : AddCommGroup W.toAffine.Point := by infer_instance
#synth AddCommGroup W.toAffine.Point
#synth SMul ℕ W.toAffine.Point
#check WeierstrassCurve.Affine.Point.instAddCommGroup
