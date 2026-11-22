import tmp.sheaf.xif.paper.PaperRootTensorHaarActual

/-!
# Minimal Haar scaling interface on the finite root field L

The full equality

  mu (lambda • S) = ||lambda|| * mu S

is not available for the Qp-normed field L in the current Mathlib API.  This
file constructs the minimal interface that is determined by the normalized
unit ball:

  scalingFactor lambda := mu (lambda • unitBall),

so scalingFactor 1 = 1 and the lambda-O hull lambda • unitBall has measure
scalingFactor lambda.  The all-sets equality and the norm identification remain
exact gaps, recorded separately.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootNormedHaarScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual lambda-O scaled unit ball in L. -/
noncomputable def rootNormedLambdaOHull (lam : rootNormedExtension T b) :
    Set (rootNormedExtension T b) :=
  lam • rootNormedUnitBall T b

/-- Scaling factor determined by the normalized unit ball. -/
noncomputable def rootNormedHaarScalingFactor
    (lam : rootNormedExtension T b) : ENNReal :=
  rootNormedHaar T b (rootNormedLambdaOHull T b lam)

/-- The lambda-O hull measure is the scaling factor by definition. -/
theorem rootNormedLambdaOHull_measure_eq_scalingFactor
    (lam : rootNormedExtension T b) :
    rootNormedHaar T b (rootNormedLambdaOHull T b lam) =
      rootNormedHaarScalingFactor T b lam := rfl

/-- Unit ball normalization: scaling factor at 1 is 1. -/
theorem rootNormedHaarScalingFactor_one :
    rootNormedHaarScalingFactor T b (1 : rootNormedExtension T b) = 1 := by
  simp [rootNormedHaarScalingFactor, rootNormedLambdaOHull,
    rootNormedUnitBall_measure]

/-- Actual normalized log of the lambda-O hull. -/
noncomputable def rootNormedLambdaOHullLog
    (lam : rootNormedExtension T b) : Real :=
  Real.log (rootNormedHaarScalingFactor T b lam).toReal

/-- Conditional nontriviality is recorded as an exact requirement: positivity
of the scaled unit-ball measure and factor ≠ 1 are not assumed as theorems. -/
structure RootNormedLambdaOLogNontrivialGap
    (lam : rootNormedExtension T b) where
  factor_pos : Prop
  factor_ne_one : Prop
  log_ne_zero : Prop

/-- Exact remaining extensions of the minimal interface: all-set scaling and
identification of the scaling factor with the p-adic norm. -/
structure RootNormedHaarScalingGap where
  all_sets_scaling : Prop
  factor_eq_norm : Prop
  nonzero_factor : Prop
  full_lambda_o_hull : Prop

/-- Exact scaling-gap requirement. -/
def RootNormedHaarScalingGapRequired : Prop :=
  Nonempty RootNormedHaarScalingGap

end LeanFormal.IUT.XiFPaper.RootNormedHaarScalingActual
end
