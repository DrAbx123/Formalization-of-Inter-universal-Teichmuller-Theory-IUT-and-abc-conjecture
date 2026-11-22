import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualReducedActual
import tmp.sheaf.xif.paper.S3132ThetaSideComparisonRegionBundleActual
import tmp.sheaf.xif.paper.S3132ThetaSideModelComparisonDataActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedPilotComparisonActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedCorollary312DataActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual
import tmp.sheaf.xif.paper.S3132RootedScalingDataFormulaActual

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
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual

/-!
# Theta-side H5: q-side signed comparison slot (adapted from SourceQSideComparison)

PRIOR ART (one line): LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceQSideComparison.lean
sourceQSideNormalizedValue:88, sourceSetVolume_possibleImage_eq_iSup_sourceQSide:96,
sourceSetVolume_possibleImage_ge_sourceQSide:108, sourceSetVolume_possibleImage_ge_ofReal_of_sourceQSide_le:125,
sourceQSideNormalizedValue_neg_iff:140, sourceUnitRegionHaarInterface_hqSlot_of_sourceQSide_le:184
-> ADAPT: the q-side signed value is supplied by that interface (not re-proved here); we keep it as an
explicit H5 slot and use the signed comparison shape qSigned <= -thetaMagnitude.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **H5 slot:** the q-side signed comparison entry from the SourceQSideComparison interface. -/
structure ThetaSideQSideSlot where
  qSigned : ℝ
  q_negative : qSigned < 0
  q_le_thetaSigned : qSigned ≤ -modelThetaValue M

/-- The H5 slot yields the adapted Corollary 3.12 comparison payload. -/
def thetaSideQSideSlot_comparisonData (S : ThetaSideQSideSlot M) :
    AdaptedCorollary312ComparisonData :=
  modelComparisonData M S.qSigned (neg_pos.mpr S.q_negative) S.q_le_thetaSigned

/-- The payload's q pilot magnitude is the positive q magnitude. -/
theorem thetaSideQSideSlot_comparisonData_qPilot_value (S : ThetaSideQSideSlot M) :
    (thetaSideQSideSlot_comparisonData M S).qPilot.value = -S.qSigned :=
  modelComparisonData_qPilot_value M S.qSigned (neg_pos.mpr S.q_negative) S.q_le_thetaSigned

/-- The H5 slot yields the adapted Corollary 3.12 inequality. -/
theorem thetaSideQSideSlot_corollary312 (S : ThetaSideQSideSlot M) :
    AdaptedCorollary312Inequality
      (thetaSideQSideSlot_comparisonData M S).thetaPilot
      (thetaSideQSideSlot_comparisonData M S).qPilot :=
  AdaptedCorollary312ComparisonData.corollary312 _

#check ThetaSideQSideSlot
#check thetaSideQSideSlot_comparisonData
#check thetaSideQSideSlot_comparisonData_qPilot_value
#check thetaSideQSideSlot_corollary312

end LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
end