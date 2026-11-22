import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual

/-! # Actual Haar scaling object for the field-scaled root hull -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact local Haar scaling factor for lambda_b O versus O. -/
noncomputable def rootThetaFieldLambdaHaarFactor
    (b : Bad (nativePlaceSelection T)) : ENNReal :=
  rootExtensionHaar T b (rootThetaFieldLambdaO T b) /
    rootExtensionHaar T b (rootExtensionUnitBall T b)


/-- Unit-norm scaling has actual Haar factor one. -/
theorem rootThetaFieldLambdaHaarFactor_eq_one_of_norm_one
    (b : Bad (nativePlaceSelection T))
    (h : ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ = 1) :
    rootThetaFieldLambdaHaarFactor T b = 1 := by
  unfold rootThetaFieldLambdaHaarFactor
  rw [rootThetaFieldLambdaO_eq_closedBall, h]
  change (rootExtensionHaar T b) (Metric.closedBall (0 : rootNormedExtension T b) 1) /
    (rootExtensionHaar T b) (Metric.closedBall (0 : rootNormedExtension T b) 1) = 1
  exact ENNReal.div_self
    (ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) 1 (by norm_num)))
    (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) 1))

/-- Exact local scaling equation: mu(lambda O) = factor * mu(O). -/
theorem rootThetaFieldLambdaO_measure_eq_factor
    (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (rootThetaFieldLambdaO T b) =
      rootThetaFieldLambdaHaarFactor T b *
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  unfold rootThetaFieldLambdaHaarFactor
  rw [ENNReal.div_mul_cancel]
  · show rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0
    exact ne_of_gt (rootExtensionUnitBall_measure_pos T b)
  · show rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤
    exact ne_of_lt (rootExtensionUnitBall_measure_lt_top T b)

/-- Local lambda-O measure is positive. -/
theorem rootThetaFieldLambdaO_measure_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < rootExtensionHaar T b (rootThetaFieldLambdaO T b) := by
  rw [rootThetaFieldLambdaO_eq_closedBall]
  apply rootExtensionClosedBall_measure_pos
  have hpos : (0 : Real) < (rootImageRadius T b : Real) := by
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  rwa [rootImageRadius_eq_norm_fieldLambda] at hpos

/-- Local lambda-O measure is finite. -/
theorem rootThetaFieldLambdaO_measure_lt_top
    (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (rootThetaFieldLambdaO T b) < ⊤ := by
  rw [rootThetaFieldLambdaO_eq_closedBall]
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

/-- Product field-scaled hull measure is positive finite. -/
theorem rootExtensionProductFieldScaledHull_measure_pos_lt_top :
    0 < rootExtensionProductHaar T (rootExtensionProductFieldScaledHull T) ∧
      rootExtensionProductHaar T (rootExtensionProductFieldScaledHull T) < ⊤ := by
  rw [rootExtensionProductFieldScaledHull_eq_imageHull]
  exact rootExtensionProductImageHull_measure_pos_lt_top T

/-- Actual normalized log of the product field-scaled hull, relative to the
product unit ball. -/
noncomputable def rootExtensionProductFieldScaledHullLog : Real :=
  rootExtensionProductNormalizedLog T (rootExtensionProductFieldScaledHull T)

/-- Definitional log-ratio formula for the field-scaled hull. -/
theorem rootExtensionProductFieldScaledHullLog_eq :
    rootExtensionProductFieldScaledHullLog T =
      Real.log (rootExtensionProductHaar T
        (rootExtensionProductFieldScaledHull T)).toReal -
      Real.log (rootExtensionProductHaar T
        (rootExtensionProductUnitBall T)).toReal :=
  rfl

/-- Candidate exact p-adic modulus: d-th power of the norm, matching the
one-dimensional direction audit (factor = norm, not inverse). -/
noncomputable def rootThetaFieldLambdaNormModulus
    (b : Bad (nativePlaceSelection T)) : ENNReal :=
  ENNReal.ofReal (‖(rootThetaFieldLambda T b :
    rootNormedExtension T b)‖ ^
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))

/-- Exact identification object: the actual local Haar factor equals the d-th
power p-adic norm modulus.  This is a Prop object, not a fake equality. -/
def RootThetaFieldHaarNormFactorIdentification
    (b : Bad (nativePlaceSelection T)) : Prop :=
  rootThetaFieldLambdaHaarFactor T b = rootThetaFieldLambdaNormModulus T b

end LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingHaarActual

end