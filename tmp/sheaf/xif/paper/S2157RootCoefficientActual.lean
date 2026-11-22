import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
noncomputable section
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S2157RootCoefficientActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Actual root coefficient generator carrier: the normed ambient of the actual
root-stack extension. -/
abbrev s2157RootCarrier : Type :=
  rootNormedAmbient T b
/-- The actual root coefficient generator: the actual 2l-th root element. -/
noncomputable def s2157RootCoefficientGenerator : s2157RootCarrier T b :=
  rootNormedElement T b
/-- The generator norm is p^(-(paper root coefficient)), not p^(-order),
conditional on the normalized completion coefficient being the actual order
(the e = 1 normalization). -/
theorem s2157RootCoefficientGenerator_norm
    (hcNorm : LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
      = ((qVFamily T b).order : Real)) :
    ‖s2157RootCoefficientGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamPaperRootCoefficient T b)) := by
  unfold s2157RootCoefficientGenerator qVFamPaperRootCoefficient
  change rootNormedElementNorm T b = _
  rw [rootNormedElementNorm_eq_p_rpow, hcNorm]
  congr 1
  ring
/-- Exact target-level bridge missing: the root-stack generator has the
required norm, but lives in rootNormedExtension, not CommonPrimeCompletion. -/
def s2157CompletionCarrierBridgeMissing : Prop :=
  Nonempty (s2157RootCarrier T b)
#print axioms s2157RootCoefficientGenerator_norm
end LeanFormal.IUT.XiFPaper.S2157RootCoefficientActual
end
