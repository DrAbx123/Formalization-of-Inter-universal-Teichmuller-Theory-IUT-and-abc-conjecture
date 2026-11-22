import tmp.sheaf.xif.paper.Mzk1URThetaHthetaActual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartLocalizeSwapActual

/-! Batch 14c audit probe (lane=audit): independent axiom recheck of the two
post-snapshot greens:
  * Mzk1URThetaHthetaActual (src 22:57:03 / olean 22:57:57), conditional htheta;
  * Mzk1G1FermatChartLocalizeSwapActual (src 22:57:19 / olean 22:58:40),
    chart-level x<->y swap only (no localization iso).
Read-only probe: no declarations, only #print axioms. -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual.ur_htheta_of_scaling
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual.ur_htheta_of_halfScalingData
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual.ur_thetaCoeff_eq_neg_localNormOrder
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartLocalizeSwapActual.swapChart_chartR
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartLocalizeSwapActual.swapChart_chartR2
