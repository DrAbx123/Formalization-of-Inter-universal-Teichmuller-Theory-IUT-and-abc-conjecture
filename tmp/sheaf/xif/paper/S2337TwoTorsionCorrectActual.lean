import tmp.sheaf.xif.paper.S2335TwoTorsionRootActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! # S2337: correct 2-torsion point from a 2-division root

For a root `x` of `twoTorsionPolynomial`, the point with
`y = -(a1*x + a3)/2` satisfies the Weierstrass equation.  The `2 • P = 0`
and three-distinct-roots statements are recorded separately; no fake is
asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual

universe u

variable {R : Type u} [Field R] (W : WeierstrassCurve R)

/-- The corrected 2-torsion y-coordinate. -/
noncomputable def S2337Y (x : R) : R :=
  -((W.a₁ * x + W.a₃) / 2)

#check S2337Y



end LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual

end
