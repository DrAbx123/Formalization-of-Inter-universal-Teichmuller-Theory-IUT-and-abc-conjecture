import tmp.sheaf.xif.paper.S3132ThetaSideCertificateSignedShapeActual
import tmp.sheaf.xif.paper.S3132ThetaSideHullSlotWiringActual
import tmp.sheaf.xif.paper.S3132ThetaSideQSideSlotWiringActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideCertificateSignedShapeActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleV2Actual

/-!
# Theta-side comparison-region bundle V2 (explicit named hypotheses, no closure claims)

PRIOR ART (one line each):
- H4 hull slot: CertificateHullWiring.lean:106/155/272 + CardAMPLThetaBoundSupply.lean:78/94/116/125 -> ADAPT (see S3132ThetaSideHullSlotWiringActual);
- signed certificate shape: CertificateHullWiringSigned.lean:132 -> ADAPT (see S3132ThetaSideCertificateSignedShapeActual);
- H5 q slot: SourceQSideComparison.lean:88/96/108/125/140/184 -> ADAPT (see S3132ThetaSideQSideSlotWiringActual);
- H1 data: stage4 S3136ModelSourceClauseActual LGPModelSourceClauseMissing;
- H2: S3132ThetaSideSharpResidualReducedActual ModelWeightedRootedIdentity;
- H3 coefficient identification hc: S3132RootedScalingDataFormulaActual (explicit hypothesis).
FROZEN OBSTACLES (recorded, not bypassed): CardQCMPComparison.lean:50-68 (q family arithmetic-only, no
object-level target, hull_le_theta = registered certificate-hull/AMPL boundary).
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **Bundle V2:** H1 data + H3 coefficient identification + H2 weighted identity + H4 hull slot + H5 q slot. -/
structure ThetaSideBundleV2 where
  hc : ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
    rootHalfCoefficient (lgpModelNativeData M) b =
      paperRootCoefficientFamily (lgpModelNativeData M) b
  weighted : ModelWeightedRootedIdentity M
  hullSlot : ThetaSideHullBoundSlot M
  qSlot : ThetaSideQSideSlot M

/-- The bundle's comparison payload (from H5 + H2). -/
def ThetaSideBundleV2.comparisonData (B : ThetaSideBundleV2 M) :
    AdaptedCorollary312ComparisonData :=
  thetaSideQSideSlot_comparisonData M B.qSlot

/-- The payload's Theta pilot magnitude is the canonical model readout. -/
theorem ThetaSideBundleV2.comparisonData_thetaPilot_value (B : ThetaSideBundleV2 M) :
    B.comparisonData.thetaPilot.value = modelThetaValue M :=
  modelComparisonData_thetaPilot_value M B.qSlot.qSigned (neg_pos.mpr B.qSlot.q_negative)
    B.qSlot.q_le_thetaSigned

/-- The bundle yields the adapted Corollary 3.12 inequality. -/
theorem ThetaSideBundleV2.corollary312 (B : ThetaSideBundleV2 M) :
    AdaptedCorollary312Inequality B.comparisonData.thetaPilot B.comparisonData.qPilot :=
  AdaptedCorollary312ComparisonData.corollary312 _

#check ThetaSideBundleV2
#check ThetaSideBundleV2.comparisonData
#check ThetaSideBundleV2.comparisonData_thetaPilot_value
#check ThetaSideBundleV2.corollary312

end LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleV2Actual
end