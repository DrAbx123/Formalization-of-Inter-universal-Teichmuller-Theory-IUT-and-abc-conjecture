import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
open Polynomial MvPolynomial WeierstrassCurve
#check WeierstrassCurve.Affine.CoordinateRing.basis
#check WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing
#check WeierstrassCurve.Affine.CoordinateRing.mk
#check WeierstrassCurve.Affine.polynomial
#check MvPolynomial.finSuccEquiv
#check MvPolynomial.finOneEquiv
#check AdjoinRoot.lift
#check AdjoinRoot.mk