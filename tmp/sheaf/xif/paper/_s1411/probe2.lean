import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

open Polynomial WeierstrassCurve

#check WeierstrassCurve.Jacobian.toAffine_toJacobian
#check WeierstrassCurve.Affine.toJacobian_toAffine
#check WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply
#check WeierstrassCurve.Affine.Point.toJacobian
#check WeierstrassCurve.Affine.Point.toJacobian_some
#check WeierstrassCurve.Affine.Point.toJacobian_zero
#check WeierstrassCurve.Jacobian.Point.fromAffine
#check WeierstrassCurve.Jacobian.Point.fromAffine_some
#check Quotient.sound
#check Quotient.exact
#check AddEquiv.map_eq_zero_iff
#check map_zsmul
#check natCast_zsmul
#check WeierstrassCurve.Affine.Point.some.injEq
#check WeierstrassCurve.Affine.Point.some_ne_zero
