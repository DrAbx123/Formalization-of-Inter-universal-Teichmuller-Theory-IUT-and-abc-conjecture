import tmp.sheaf.xif.paper.S718RootImageRadiusLowerActual
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S727RootThetaOneNormFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.S718RootImageRadiusLowerActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S712RootLabelRegionNormActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual closed form of the root image radius in terms of c_norm. -/
theorem rootImageRadius_eq_cNorm_rpow :
    (rootImageRadius T b : Real) =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) :=
  S709RootImageRadiusFormulaActual.rootImageRadius_eq_p_rpow (l := l) T b

/-- Exact correction bridge: c_norm = order. -/
def NormalizedOrderCorrectionZero : Prop :=
  qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real)

/-- If the normalized coefficient equals the qVFamily order, the S712
root-image-radius lower bound follows from the actual S709 closed form. -/
theorem rootImageRadiusLowerBound_order_of_correction
    (hcorr : NormalizedOrderCorrectionZero (l := l) T b) :
    S712RootLabelRegionNormActual.RootImageRadiusLowerBound (l := l) T b := by
  unfold S712RootLabelRegionNormActual.RootImageRadiusLowerBound
    rootLabelRegionRadiusCandidate
  rw [rootImageRadius_eq_cNorm_rpow]
  rw [hcorr]

/-- Exact corrected lower bound with c_norm, without the order correction. -/
theorem rootImageRadiusLowerBound_cNorm :
    Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)))
      ≤ (rootImageRadius T b : Real) := by
  rw [rootImageRadius_eq_cNorm_rpow]

end LeanFormal.IUT.XiFPaper.S727RootThetaOneNormFormulaActual

end
