import tmp.sheaf.xif.paper.S3132ThetaSideComparisonRegionBundleV2Actual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

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
open LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleV2Actual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideBundleWithDataActual

/-!
# STEP 0 prior-art: ThetaSideBundleV2|ModelWeightedRootedIdentity|ThetaSideHullBoundSlot|ThetaSideQSideSlot|paperRootCoefficientFamily -> hits S3132ThetaSideComparisonRegionBundleV2Actual + H4/H5 slot files + BadPlacePaperRootThetaHullActual:36 -> REUSE (bundle data record with explicit H1 field; no re-proof).

# Theta-side bundle with explicit H1 data field (data record; no closure claims)

Consolidates the H1 minimal clause data M with the named hypotheses hc (H3), R2
(H2), H4 slot, H5 slot as one record, and proves the class A projection to the
adapted Corollary 3.12 comparison payload.  The paper's actual H1/H4 comparisons
are NOT proved here.  Registry frozen 14041.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Bundle: H1 data M + named hypotheses hc (H3), R2 (H2), H4 slot, H5 slot. -/
structure ThetaSideBundleWithData where
  hc : ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
    rootHalfCoefficient (l := l) (lgpModelNativeData M) b =
      paperRootCoefficientFamily (lgpModelNativeData M) b
  weighted : ModelWeightedRootedIdentity M
  hullSlot : ThetaSideHullBoundSlot M
  qSlot : ThetaSideQSideSlot M

/-- The bundle yields the adapted Corollary 3.12 comparison payload with Theta
magnitude the canonical rooted readout. -/
theorem ThetaSideBundleWithData.comparisonData_corollary312
    (B : ThetaSideBundleWithData M) :
    ∃ d : AdaptedCorollary312ComparisonData,
      d.thetaPilot.value = modelThetaValue M ∧
      AdaptedCorollary312Inequality d.thetaPilot d.qPilot := by
  refine ⟨thetaSideQSideSlot_comparisonData M B.qSlot, ?_, ?_⟩
  · exact modelComparisonData_thetaPilot_value M B.qSlot.qSigned
      (neg_pos.mpr B.qSlot.q_negative) B.qSlot.q_le_thetaSigned
  · exact thetaSideQSideSlot_corollary312 M B.qSlot

#check ThetaSideBundleWithData
#check ThetaSideBundleWithData.comparisonData_corollary312

end LeanFormal.IUT.XiFPaper.S3132ThetaSideBundleWithDataActual
end