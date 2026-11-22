import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
open WeierstrassCurve
#check WeierstrassCurve.Affine.equation_iff
#check WeierstrassCurve.Affine.equation_iff
example (F : Type) [Field F] (x y : F) :
  (WeierstrassCurve.mk (0:F) 0 1 (-1) 0).toAffine.Equation x y ↔ y^2 + y = x^3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  ring_nf