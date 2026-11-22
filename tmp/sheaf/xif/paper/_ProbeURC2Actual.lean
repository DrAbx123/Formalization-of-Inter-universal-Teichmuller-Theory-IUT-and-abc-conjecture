/- U-R C2 audit probe (lane=audit, batch 9b). Axiom check only; no new math. -/
import tmp.sheaf.xif.paper.Mzk1URPacketActual
import tmp.sheaf.xif.paper.Mzk1URRootMassActual
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullActual
import tmp.sheaf.xif.paper.Mzk1URThetaPacketInstanceActual
import tmp.sheaf.xif.paper.Mzk1URJ2Actual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionSourceActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import Mathlib.Tactic

-- item 1: packet carrier has no theorem; check the derived defs are constants
#check @LeanFormal.IUT.XiFPaper.Mzk1URPacketActual.urP
#check @LeanFormal.IUT.XiFPaper.Mzk1URPacketActual.urIst
#check @LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual.p6Place

-- item 2: root mass normalization identities
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual.normalizedLogMass_smul_units
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual.normalizedLogMass_kummer_root

-- item 3: Phi source data and packet-hull inclusion
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual.p6_possibleImages_subset_packetHull
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionSourceActual.phiActionSourceData
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URPacketActual.urPhi_preserves
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URPacketActual.urPhi_nonempty

-- item 4: q-reading order formula
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URPacketActual.ur_qReading_formula
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual.urRootTheta_order
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual.urRootTheta_order_base

-- item 5: negative q terms, theta mass, C1, weights, per-b inequality
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual.urRootTheta_log_norm_eq_neg_order
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual.urRootTheta_log_norm_eq_neg_shift
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual.urRootTheta_log_norm_eq_q
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual.urRootTheta_mass
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketInstanceActual.ulThetaPacketV_eq_neg_order
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketInstanceActual.ulThetaPacketV_eq_neg_shift
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketInstanceActual.ulThetaPacketV_le_paperC1_uncond
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual.ur_negM_le_Htheta
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual.ur_perB_containment
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual.ur_thetaHull_magnitude
#print axioms LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualTargetWeight_nonneg

-- item 6: Mzk1URJ1Actual and URThetaRegion both FAIL in watchdog; no probe possible.
