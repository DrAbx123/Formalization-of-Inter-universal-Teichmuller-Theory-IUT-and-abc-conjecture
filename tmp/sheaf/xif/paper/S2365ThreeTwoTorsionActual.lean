import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import Mathlib.Algebra.CubicDiscriminant

-- S2365: three distinct 2-torsion points -- exact missing audit.
-- Need: (2:R)!=0, base-change W to AlgebraicClosure R, three distinct roots
-- from Cubic.discr_ne_zero_iff_roots_nodup, S2353/S2354/S2358 at each root,
-- then Affine.Point.baseChange + Projective.Point.toAffineAddEquiv +
-- pointTransport_galois (S1550). No witness constructed.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2365ThreeTwoTorsionActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual
open LeanFormal.IUT.XiFPaper.S2353TwoTorsionEquationActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual

universe u

#check Cubic.roots
#check Cubic.splits_iff_roots_eq_three
#check Cubic.discr_ne_zero_iff_roots_nodup
#check WeierstrassCurve.twoTorsionPolynomial
#check S2354Point

end LeanFormal.IUT.XiFPaper.S2365ThreeTwoTorsionActual

end
