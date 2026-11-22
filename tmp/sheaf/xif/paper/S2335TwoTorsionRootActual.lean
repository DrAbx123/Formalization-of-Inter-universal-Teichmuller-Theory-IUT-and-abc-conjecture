import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import tmp.sheaf.xif.paper.S2333ThreeTwoTorsionActual

/-! # S2335: twoTorsionPolynomial versus Equation x 0

`twoTorsionPolynomial = <4, b2, 2*b4, b6>` and its eval is
`4*(x^3 + a2*x^2 + a4*x + a6) + (a1*x + a3)^2`, while
`W.Equation x 0` is `x^3 + a2*x^2 + a4*x + a6 = 0`.

Hence `twoTorsionPolynomial.eval x = 0` is NOT equivalent to `W.Equation x 0`
unless `a1*x + a3 = 0` (or characteristic 2).  The Mathlib root description
is for the general 2-torsion x-coordinate, not for y = 0.  This is the exact
definitional obstruction to the S2333 route; no fake equivalence is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual

open WeierstrassCurve

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The exact evaluation identity for the 2-torsion polynomial. -/
theorem S2335TwoTorsionPolynomial_eval (x : R) :
    W.twoTorsionPolynomial.toPoly.eval x =
      (W.a₁ * x + W.a₃) ^ 2 +
        4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

#print axioms S2335TwoTorsionPolynomial_eval

end LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual

end
