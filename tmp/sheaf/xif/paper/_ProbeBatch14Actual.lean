import tmp.sheaf.xif.paper.Mzk1P1ValuativeActual
import tmp.sheaf.xif.paper.Mzk1P1UniversallyClosedActual
import tmp.sheaf.xif.paper.Mzk1P6P5ThetaHullControl2
import tmp.sheaf.xif.paper.Mzk1URThetaPacketCarrierActual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartSwapActual

/-! Batch 14 audit probe (lane=audit): independent axiom recheck of the
post-14:46Z evidence:
  * P1Valuative existence (src 22:48:47 / olean 22:49:52) + chart_coord_compat;
  * P1UniversallyClosed (src 22:51:00 / olean 22:51:44), the new
    UniversallyClosed factor of IsProper;
  * P6P5ThetaHullControl2 (src 22:47:51 / olean 22:49:11);
  * URThetaPacketCarrierActual (src 22:48:31 / olean 22:50:16);
  * FermatChartSwapActual (src 22:40:22 / olean 22:41:04, re-check of P13b).
Read-only probe: no declarations, only #print axioms. -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeActual.valuativeCriterion_existence
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeActual.chart_coord_compat
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P1UniversallyClosedActual.p1GluedToBase_universallyClosed
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ulHpkt
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketCarrierActual.urThetaPossibleImages_subset_packetHull
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSwapActual.ModelSwapEquiv
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSwapActual.modelSwap_isStandardSmooth
