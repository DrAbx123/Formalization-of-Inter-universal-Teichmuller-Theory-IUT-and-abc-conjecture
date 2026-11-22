/- Probe (read-only): round-4 axiom audit part 3 (henry/andrew/emmy re-run + HTF5 fix). -/
import tmp.sheaf.xif.paper.Mzk1G1GKDeltaActual
import tmp.sheaf.xif.paper.Mzk1HTF4StageAActual
import tmp.sheaf.xif.paper.Mzk1HTF4StageBActual
import tmp.sheaf.xif.paper.Mzk1HTF5StageAActual
import tmp.sheaf.xif.paper.Mzk1G1B1HoutActual
import tmp.sheaf.xif.paper.Mzk1G1B1SmoothCriterionSubmActual

open LeanFormal.IUT.XiFPaper

-- henry: GKDelta boundary distances
#print axioms Mzk1G1GKDeltaActual.continuous_chordalBoundaryDist
#print axioms Mzk1G1GKDeltaActual.continuous_padicBoundaryDist
#print axioms Mzk1G1GKDeltaActual.chordalBoundaryDist_pos
#print axioms Mzk1G1GKDeltaActual.padicBoundaryDist_pos

-- andrew: HTF4 A/B, HTF5 A
#print axioms HTF4StageAActual.routeF4_of_divisorHeight
#print axioms HTF4StageAActual.F4DivisorHeightData.hE_le_r
#print axioms HTF4StageAActual.F4DivisorHeightData.hE_le_kappa
#print axioms HTF4StageBActual.routeF4_of_actualDivisor
#print axioms HTF5StageAActual.f5_to_f6_core
#print axioms HTF5StageAActual.f5_to_f6_core_choice

-- emmy: B1 hout / smooth criterion
#print axioms Mzk1G1B1HoutActual.hout
#print axioms Mzk1G1B1HoutActual.compl_range_localChartInf_eq_p1Zero
#print axioms Mzk1G1B1SmoothCriterionSubmActual.pderiv_hAtT
#print axioms Mzk1G1B1SmoothCriterionSubmActual.smoothModelIdx_injective
#print axioms Mzk1G1B1SmoothCriterionSubmActual.smoothModelRel_zero
