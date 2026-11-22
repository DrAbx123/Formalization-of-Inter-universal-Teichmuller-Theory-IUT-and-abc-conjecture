import tmp.sheaf.xif.paper.S2376ThreeRootsActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import tmp.sheaf.xif.paper.S2354TwoTorsionPointsActual
import tmp.sheaf.xif.paper.S2353TwoTorsionEquationActual
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
-- S2385: root membership -> eval=0 on base-changed W; then point transport.
-- Exact remaining: (1) twoTorsionPolynomial_map identity; (2) mem_roots_iff ->
-- toPoly.eval=0 for W.map (algebraMap R (AlgebraicClosure R)); (3) apply
-- S2353/S2354/S2358 at each root; (4) Affine.Point.baseChange +
-- Projective.Point.toAffineAddEquiv + pointTransport_galois (S1550).
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
namespace LeanFormal.IUT.XiFPaper.S2385TwoTorsionTransportActual
open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual
open LeanFormal.IUT.XiFPaper.S2353TwoTorsionEquationActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
universe u
#check S2376ThreeDistinctRoots
#check Cubic.mem_roots_iff
#check S2353_equation
#check S2354Point
#check S2358_two_nsmul
#check pointTransport_galois
end LeanFormal.IUT.XiFPaper.S2385TwoTorsionTransportActual
end