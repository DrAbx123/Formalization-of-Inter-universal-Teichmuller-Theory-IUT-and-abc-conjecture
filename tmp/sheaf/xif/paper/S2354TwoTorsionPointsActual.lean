import tmp.sheaf.xif.paper.S2353TwoTorsionEquationActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! # S2354: 2-torsion points from 2-division roots -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual
open LeanFormal.IUT.XiFPaper.S2353TwoTorsionEquationActual

universe u

variable {R : Type u} [Field R] [Nontrivial R]
variable (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

/-- The 2-torsion affine point attached to a 2-division root. -/
noncomputable def S2354Point (h2 : (2 : R) ≠ 0) (x : R)
    (hx : W.twoTorsionPolynomial.toPoly.eval x = 0) : W.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (S2353_equation W h2 x hx)


#check S2354Point

end LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual

end
