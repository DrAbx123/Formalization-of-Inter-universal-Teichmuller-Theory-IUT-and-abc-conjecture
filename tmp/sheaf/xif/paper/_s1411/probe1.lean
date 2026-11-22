import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

open Polynomial WeierstrassCurve

#check WeierstrassCurve.Affine.toJacobian
#check WeierstrassCurve.Jacobian.Point.fromAffine
#check WeierstrassCurve.Jacobian.equiv_zero_of_Z_eq_zero
#check WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv
#check WeierstrassCurve.Jacobian.Point.zero_point
#check WeierstrassCurve.Jacobian.Point.ext_iff
#check WeierstrassCurve.evalDivisionPolynomial
#check WeierstrassCurve.Affine.Point.some
#check WeierstrassCurve.Affine.Point.toJacobian
#check WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
#check WeierstrassCurve.Jacobian.nonsingularLift_iff
#check WeierstrassCurve.Jacobian.Point.nonsingular
#check WeierstrassCurve.Affine.Point.toJacobianAddEquiv
