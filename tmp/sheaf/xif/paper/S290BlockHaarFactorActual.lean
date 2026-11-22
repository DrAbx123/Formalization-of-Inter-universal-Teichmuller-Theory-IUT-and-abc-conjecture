import tmp.sheaf.xif.paper.S288ThetaScalingHaarFactorActual
import tmp.sheaf.xif.paper.S284RootUniformizerFactorActual

/-! # S290: block thetaScalingHaarFactor at uniformizer and prime

Using S288 (block factor = root factor) and S284 (root uniformizer factor =
||pi||^d), prove the block uniformizer formula.  The prime formula follows from
the actual root prime factor theorem.

No inequality/no fake factor/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S290BlockHaarFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.S288ThetaScalingHaarFactorActual
open LeanFormal.IUT.XiFPaper.S284RootUniformizerFactorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Block Haar factor at the chosen root uniformizer equals ||pi||^d. -/
theorem thetaScalingHaarFactor_uniformizer_eq_norm_pow :
    (thetaScalingHaarFactor (T := T) (b := b)
      (rootUniformizerField T b : rootNormedExtension T b)
      (Units.ne_zero (rootUniformizerField T b)) : ENNReal) =
      ENNReal.ofReal
        ((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
          Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [thetaScalingHaarFactor_eq_rootHaarFactor]
  exact rootHaarFactor_uniformizer_eq_norm_pow (T := T) (b := b)

/-- Block Haar factor at the rational prime unit equals ||p||^d. -/
theorem thetaScalingHaarFactor_prime_eq_norm_pow :
    (thetaScalingHaarFactor (T := T) (b := b)
      (rootPrimeFieldUnit T b : rootNormedExtension T b)
      (Units.ne_zero (rootPrimeFieldUnit T b)) : ENNReal) =
      ENNReal.ofReal
        ((‖(algebraMap ℚ_[(qVFamTensorP T b)]
              (rootNormedExtension T b) (qVFamTensorP T b) :
            rootNormedExtension T b)‖) ^
          Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [thetaScalingHaarFactor_eq_rootHaarFactor]
  exact rootHaarFactor_prime_eq_norm_pow (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.S290BlockHaarFactorActual

end
