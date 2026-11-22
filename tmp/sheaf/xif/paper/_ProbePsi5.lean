import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
example : W.ψ (5:ℤ) = C (W.preΨ (5:ℤ)) := by
  rw [show (5:ℤ) = 2*2+1 by norm_num, W.ψ_odd 2]
  norm_num [W.ψ_four, W.ψ_three, W.ψ_two, W.ψ_one, W.preΨ_odd 2, W.preΨ_four, W.preΨ_three, W.preΨ_two, W.preΨ_one, W.preΨ_zero]
  ring
