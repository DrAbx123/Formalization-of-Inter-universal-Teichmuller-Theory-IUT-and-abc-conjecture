import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
-- S2415 exact missing: S2412 points live on W.map (algebraMap R (AlgebraicClosure R));
-- SideKPoint T b uses WKproj T b = (kSideCurve T).baseChange(Kv).toProjective.baseChange(LK).
-- Need (1) identify W with T.arithmetic.curve and base change F -> Fv -> LF/LK;
-- (2) S1493 curveEq to identify kSideCurve base change with arithmetic curve base change;
-- (3) S1550 pointTransport goes SideFPoint -> SideKPoint; transport the three points;
-- (4) prove preservation of 2-torsion/distinctness/nonzero/IsGaloisFixed.
-- No witness constructed.
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
namespace LeanFormal.IUT.XiFPaper.S2415SideKPointActual
open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2412ThreePointsTransportActual
open LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual
universe u
#check S2412ThreePoints
#check S2414_point_ne
#check S2414_point_ne_zero
#check pointTransport
#check pointTransport_galois
#check S1550TatePointComparisonFromClosureActual.WFproj
#check S1550TatePointComparisonFromClosureActual.WKproj
end LeanFormal.IUT.XiFPaper.S2415SideKPointActual
end