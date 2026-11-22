/- Probe (read-only): round-4 axiom audit for recently DONE declarations.
Requested by Lead 2026-11-17 (sophie support).  Covers sophie, andrew, henry, emmy;
grace's A3 files are absent from the repo at probe time (recorded as missing). -/
import tmp.sheaf.xif.paper.Mzk1G1GKDeltaActual
import tmp.sheaf.xif.paper.Mzk1HTF4StageAActual
import tmp.sheaf.xif.paper.Mzk1HTF4StageBActual
import tmp.sheaf.xif.paper.Mzk1G1B1HoutActual
import tmp.sheaf.xif.paper.Mzk1G1B1SmoothCriterionSubmActual
import tmp.sheaf.xif.paper.Mzk1ULHcondAssemblyActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreSupportDataActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreDiscSupportActual

open LeanFormal.IUT.XiFPaper

-- henry: GKDelta boundary distances
#print axioms Mzk1G1GKDeltaActual.continuous_chordalBoundaryDist
#print axioms Mzk1G1GKDeltaActual.continuous_padicBoundaryDist
#print axioms Mzk1G1GKDeltaActual.chordalBoundaryDist_pos
#print axioms Mzk1G1GKDeltaActual.padicBoundaryDist_pos

-- andrew: HTF4 stage A/B
#print axioms HTF4StageAActual.routeF4_of_divisorHeight
#print axioms HTF4StageAActual.F4DivisorHeightData.hE_le_r
#print axioms HTF4StageAActual.F4DivisorHeightData.hE_le_kappa
#print axioms HTF4StageBActual.routeF4_of_actualDivisor

-- emmy: B1 hout / smooth criterion
#print axioms Mzk1G1B1HoutActual.hout
#print axioms Mzk1G1B1HoutActual.compl_range_localChartInf_eq_p1Zero
#print axioms Mzk1G1B1SmoothCriterionSubmActual.pderiv_hAtT
#print axioms Mzk1G1B1SmoothCriterionSubmActual.smoothModelIdx_injective
#print axioms Mzk1G1B1SmoothCriterionSubmActual.smoothModelRel_zero

-- sophie: hcond assembly / Legendre support
#print axioms Mzk1ULHcondAssemblyActual.hcond_of_legendreTpdSupport
#print axioms Mzk1ULHcondAssemblyActual.tripodalDictionaryOfLegendreSupport
#print axioms Mzk1ULLegendreSupportDataActual.legendreSupportIncl
#print axioms Mzk1ULLegendreSupportDataActual.legendre_tpd_subset_point
#print axioms Mzk1ULLegendreDiscSupportActual.legendre_disc_primeFactors_subset
