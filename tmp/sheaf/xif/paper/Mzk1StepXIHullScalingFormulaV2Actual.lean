import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi hull exact scaling formula

Exact one-coordinate Haar scaling formula: μ(p • S) = rootPrimeHaarFactor * μ(S). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIHullScalingFormulaV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem stepxi_hull_scaling_formula (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • S) =
      rootPrimeHaarFactor T b * rootExtensionHaar T b S := by
  rw [rootPrime_smul_measure T b S, rootPrimeHaarFactor_eq_norm_pow]

theorem stepxi_hull_scaling_unit_ball :
    rootExtensionHaar T b
        ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • rootExtensionUnitBall T b) =
      rootPrimeHaarFactor T b * rootExtensionHaar T b (rootExtensionUnitBall T b) :=
  stepxi_hull_scaling_formula T b (rootExtensionUnitBall T b)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIHullScalingFormulaV2Actual

end
