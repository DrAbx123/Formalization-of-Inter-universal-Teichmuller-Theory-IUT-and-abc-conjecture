import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-! # d-dimensional p-scaling on L -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionValuedActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- d-dimensional prime scaling: μ(p • S) = ‖p‖^d * μS. -/
theorem rootPrime_smul_measure (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • S) =
      ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b)]
        (rootNormedExtension T b) (qVFamTensorP T b) :
          rootNormedExtension T b)‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) *
        rootExtensionHaar T b S := by
  letI hfin : FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensionalQp (T := T) (b := b)
  letI hns : NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionNormedSpaceQp (T := T) (b := b)
  have h := @LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (qVFamTensorP T b) (inferInstance) (rootNormedExtension T b)
    (inferInstance) hns hfin (inferInstance) (inferInstance)
    (rootExtensionHaar T b) (inferInstance) S
  calc
    rootExtensionHaar T b ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • S)
        = ((qVFamTensorP T b : ENNReal) ^ Module.finrank
            ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))⁻¹ *
            rootExtensionHaar T b S := h
    _ = ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b)]
          (rootNormedExtension T b) (qVFamTensorP T b) :
            rootNormedExtension T b)‖ ^ Module.finrank
            ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) *
          rootExtensionHaar T b S := by
      congr 1
      rw [rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p]
      rw [ENNReal.ofReal_pow (by positivity)]
      rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos), ENNReal.ofReal_natCast]
      rw [ENNReal.inv_pow]

/-- The actual prime scaling factor on the unit ball. -/
noncomputable def rootPrimeHaarFactor : ENNReal :=
  rootExtensionHaar T b
    ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
      rootExtensionUnitBall T b) /
  rootExtensionHaar T b (rootExtensionUnitBall T b)

/-- The prime scaling factor is the d-th power of the norm. -/
theorem rootPrimeHaarFactor_eq_norm_pow :
    rootPrimeHaarFactor T b =
      ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b)]
        (rootNormedExtension T b) (qVFamTensorP T b) :
          rootNormedExtension T b)‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  unfold rootPrimeHaarFactor
  rw [rootPrime_smul_measure]
  exact ENNReal.mul_div_cancel_right
    (ne_of_gt (rootExtensionUnitBall_measure_pos T b))
    (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))

end LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual

end