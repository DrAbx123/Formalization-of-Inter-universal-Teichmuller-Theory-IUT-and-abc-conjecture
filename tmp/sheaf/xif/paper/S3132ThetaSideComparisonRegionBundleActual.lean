import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualReducedActual
import tmp.sheaf.xif.paper.S3132ThetaSideModelComparisonDataActual

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
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleActual

/-!
# Paper-route Theta side: comparison-region bundle (stage4 data + weighted identity)

Consumes stage4's minimal clause data adapters (LGPModelSourceClauseMissing ->
lgpModelNativeData / lgpModelNativeDataWithHaar / lgpNativeHaarFamily) together
with the REDUCED Theta identity (R2), and packages the Corollary 3.12
comparison-region payload for the paper-route V2 consumer
(Cor312EpsilonArithmeticComparisonV2.comparisonRegion).  Component, not a paper
object; owner hull.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- The bundled comparison-region data: stage4 datum + concrete Haar family +
weighted identity (R2) + q-side signed comparison data. -/
structure ThetaSideComparisonRegionBundle (qSigned : ℝ)
    (hq : 0 < -qSigned)
    (hle : qSigned ≤ -modelThetaValue M) where
  weighted : ModelWeightedRootedIdentity M
  comparison : AdaptedCorollary312ComparisonData
  comparison_eq : comparison = modelComparisonData M qSigned hq hle
  theta_eq : comparison.thetaPilot.value = modelThetaValue M

/-- Construct the bundle from the weighted identity (R2). -/
def comparisonRegionBundle (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤ -modelThetaValue M)
    (h : ModelWeightedRootedIdentity M) :
    ThetaSideComparisonRegionBundle M qSigned hq hle :=
  { weighted := h
    comparison := modelComparisonData M qSigned hq hle
    comparison_eq := rfl
    theta_eq := modelComparisonData_thetaPilot_value M qSigned hq hle }

/-- The bundle's comparison payload satisfies the adapted Corollary 3.12
inequality. -/
theorem comparisonRegionBundle_corollary312 (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤ -modelThetaValue M)
    (h : ModelWeightedRootedIdentity M) :
    AdaptedCorollary312Inequality
      (comparisonRegionBundle M qSigned hq hle h).comparison.thetaPilot
      (comparisonRegionBundle M qSigned hq hle h).comparison.qPilot :=
  AdaptedCorollary312ComparisonData.corollary312 _

#check ThetaSideComparisonRegionBundle
#check comparisonRegionBundle
#check comparisonRegionBundle_corollary312

end LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleActual
end