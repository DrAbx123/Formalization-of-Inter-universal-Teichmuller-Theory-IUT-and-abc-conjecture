/- Independent audit probe (batch 4, lane=audit, 2026-11-16 23:39Z snapshot).
   Recomputed #print axioms for the current-attempt DONE targets audited in
   coord/AUDIT-ROUTE-20261116.md.  This file is audit-owned; it only reads
   theorems, it does not restate or strengthen them.  No sorry/axiom here. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatFiniteDegree2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveClosed2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatProperFinal2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatOmegaTransitionActual
import tmp.sheaf.xif.paper.Mzk1HullFermatGluingActual
import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import tmp.sheaf.xif.paper.Mzk1ULWeightedHullActual
import tmp.sheaf.xif.paper.Mzk1ULPacketVActual
import tmp.sheaf.xif.paper.Mzk1G1PsiTwoChartCocycleActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSupportActual

open LeanFormal.IUT.XiFPaper

-- G-A geom: rank / finite / relation (FiniteDegree2Actual, DONE 23:39:32)
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatA0Poly_monic
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatA0Ring_finite_over_U0
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatA0Ring_finrank
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatA0Ring_finite
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatA0_root_pow
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatAInfRing_finrank
#print axioms Mzk1G1FermatFiniteDegree2Actual.fermatAInf_root_pow

-- G-A closed / proper + chart covering (CurveClosed2Actual, DONE 23:39:31)
#print axioms Mzk1G1FermatCurveClosed2Actual.fermatCurve_closedImmersion
#print axioms Mzk1G1FermatCurveClosed2Actual.fermatCurve_proper
#print axioms Mzk1G1FermatCurveClosed2Actual.fermatPolynomial_relation
#print axioms Mzk1G1FermatCurveClosed2Actual.fermat_X1_pow_mem_span
#print axioms Mzk1G1FermatCurveClosed2Actual.fermat_X1_mem_of_prime

-- copy-paste re-export layer (ProperFinal2Actual, DONE 23:35:37)
#print axioms Mzk1G1FermatProperFinal2Actual.fermatCurve_proper
#print axioms Mzk1G1FermatProperFinal2Actual.fermatCurve_closedImmersion

-- G-B omega transition scalar identity (DONE 23:35:11)
#print axioms Mzk1G1FermatOmegaTransitionActual.fermatOmegaTransition

-- G-A hull: two-chart GlueData (DONE 23:35:19; def-level check only)
#print axioms Mzk1HullFermatGluingActual.twoChartGlueData

-- U-C sandwich (DONE 23:34:24)
#print axioms Mzk1UCHpktActual.uc_sandwich
#print axioms Mzk1UCHpktActual.uc_c3
#print axioms Mzk1UCHpktActual.uc_c4_from_weighted

-- U-L weighted hull (DONE 23:34:30)
#print axioms Mzk1ULWeightedHullActual.ulDivisorWeight_nonneg
#print axioms Mzk1ULWeightedHullActual.ulNormalizedWeight_sum
#print axioms Mzk1ULWeightedHullActual.ulWeightedPacketHull_eq_average
#print axioms Mzk1ULWeightedHullActual.ulWeightedPacketHull_le
#print axioms Mzk1ULWeightedHullActual.ulWeightedSum_le

-- U-L packet V / exceptional set (DONE 23:35:21)
#print axioms Mzk1ULPacketVActual.packetV_le_packetB
#print axioms Mzk1ULPacketVActual.packetExceptional_small_outside

-- G-C psi overlap cocycle (DONE 23:34:24)
#print axioms Mzk1G1PsiTwoChartCocycleActual.chartProdInv_eq_pow_mul_chartProd
#print axioms Mzk1G1PsiTwoChartCocycleActual.psi_chart_coords_mul_eq_one
#print axioms Mzk1G1PsiTwoChartCocycleActual.chartProd_eq_mul_erase

-- G-A geom support: chart structure morphisms finite/proper (SupportActual, DONE 23:45:47)
#print axioms Mzk1G1FermatSupportActual.fermatChart0Map_isFinite
#print axioms Mzk1G1FermatSupportActual.fermatChart0Map_isProper
#print axioms Mzk1G1FermatSupportActual.fermatChartInfMap_isFinite
#print axioms Mzk1G1FermatSupportActual.fermatChartInfMap_isProper
#print axioms Mzk1G1FermatSupportActual.fermatCurve_proper_support
#print axioms Mzk1G1FermatSupportActual.fermatCurve_closed_support
