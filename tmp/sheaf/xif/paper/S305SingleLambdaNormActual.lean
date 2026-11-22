import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.RootThetaValueInLUnitActual
import tmp.sheaf.xif.paper.S109QVFamNormValueActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S305SingleLambdaNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual
open LeanFormal.IUT.XiFPaper.S109QVFamNormValueActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem rootNormedElementNorm_pow_twoL_eq_qVFamNormalizedNorm :
    (rootNormedElementNorm T b) ^ (2 * l.value) =
      qVFamNormalizedNorm T b := by
  rw [rootNormedElementNorm_pow_twoL]
  rfl

theorem singleLambda_norm_eq_rootNorm_pow :
    ‖(singleLambda T b : rootNormedExtension T b)‖ =
      (rootNormedElementNorm T b) ^
        (gaussExponent (thetaLabelToSigned
          (maxThetaLabel (l := l) T b)).1) := by
  unfold singleLambda rootNormedElementNorm
  simpa using rootNormedThetaValueInL_norm (T := T) (b := b)
    (j := thetaLabelToSigned (maxThetaLabel (l := l) T b))



theorem rootNormedElementNorm_pow_twoL_eq_p_zpow :
    (rootNormedElementNorm T b) ^ (2 * l.value) =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) := by
  rw [rootNormedElementNorm_pow_twoL_eq_qVFamNormalizedNorm]
  exact qVFamNormalizedNorm_eq_p_zpow_neg_coefficient (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.S305SingleLambdaNormActual
end
