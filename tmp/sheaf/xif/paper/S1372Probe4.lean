import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
open Polynomial
open scoped Polynomial.Bivariate
namespace Probe
variable {K : Type*} [Field K] (W : WeierstrassCurve K)
#check WeierstrassCurve.Affine.CoordinateRing
#check WeierstrassCurve.Affine.FunctionField
#check WeierstrassCurve.Affine.CoordinateRing.mk
#check AdjoinRoot.mk_self
#check AdjoinRoot.evalEval_mk
#check WeierstrassCurve.Affine.evalEval_polynomial
#check WeierstrassCurve.Affine.nonsingular_iff
#check WeierstrassCurve.baseChange
#check WeierstrassCurve.Affine.baseChange
#check WeierstrassCurve.Affine.Nonsingular
#check IsFractionRing.injective
#check WeierstrassCurve.Affine.CoordinateRing.mk_ne_zero_of_natDegree_lt
#check AdjoinRoot.mk_ne_zero_of_natDegree_lt
#check WeierstrassCurve.Affine.coe_Δ'
#check WeierstrassCurve.IsElliptic
#check WeierstrassCurve.Affine.equation_iff_nonsingular
end Probe
