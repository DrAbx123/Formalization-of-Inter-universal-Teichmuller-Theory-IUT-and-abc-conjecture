import tmp.sheaf.xif.paper.S2365ThreeTwoTorsionActual
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.Basic

-- S2369: three distinct roots over the algebraic closure -- exact missing.
-- Need (2:R)!=0 and W elliptic; then W.twoTorsionPolynomial has a != 0 in K,
-- IsAlgClosed.splits gives three roots, discr != 0 gives nodup; extract x1 x2 x3.
-- Then S2353/S2354/S2358 at each root in K, and transport to SideKPoint via
-- Affine.Point.baseChange + Projective.Point.toAffineAddEquiv +
-- pointTransport_galois (S1550). No witness constructed.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2369ThreeTwoTorsionActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual
open LeanFormal.IUT.XiFPaper.S2353TwoTorsionEquationActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2365ThreeTwoTorsionActual

universe u

#check IsAlgClosed.splits
#check Cubic.splits_iff_roots_eq_three
#check Cubic.discr_ne_zero_iff_roots_nodup
#check WeierstrassCurve.baseChange
#check S2354Point

end LeanFormal.IUT.XiFPaper.S2369ThreeTwoTorsionActual

end
