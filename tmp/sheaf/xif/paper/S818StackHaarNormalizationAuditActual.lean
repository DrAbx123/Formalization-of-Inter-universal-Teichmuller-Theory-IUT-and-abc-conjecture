import tmp.sheaf.xif.paper.S809PaperLeastHullRootStackBridgeActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S818StackHaarNormalizationAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Actual log of the stack Haar of the root ball. -/
noncomputable def stackHaarBallLog : Real :=
  Real.log
    ((rootStackHaar (l := l) T b
      (Metric.closedBall (0 : rootStackExtension (l := l) T b)
        ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖)).toReal)

/-- The bridge is exactly the equality of this actual ball log with the paper
least hull log; no value of the stack Haar ball is asserted. -/
theorem stackHaarNormalizationBridge_iff :
    StackHaarNormalizationBridge (l := l) T b mu ↔
      stackHaarBallLog (l := l) T b =
        paperLeastLambdaOHullLog (l := l) T b mu := by
  unfold StackHaarNormalizationBridge stackHaarBallLog
  rfl

/-- Exact minimal condition for the bridge after the S799 formula. -/
def StackHaarBallFormulaCondition : Prop :=
  stackHaarBallLog (l := l) T b =
    paperQPilotLogLeast (l := l) T b

/-- Conditional bridge from the actual ball-log formula condition. -/
theorem stackHaarNormalizationBridge_of_formulaCondition
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b))
    (h : StackHaarBallFormulaCondition (l := l) T b) :
    StackHaarNormalizationBridge (l := l) T b mu := by
  rw [stackHaarNormalizationBridge_iff]
  rw [h]
  exact (paperLeastLambdaOHullLog_eq_formula (l := l) T b mu D).symm

/-- Exact minimal datum: completion formula data plus the actual ball-log
normalization condition. -/
def StackHaarNormalizationExactMinimal : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b)) ∧
  StackHaarBallFormulaCondition (l := l) T b

end LeanFormal.IUT.XiFPaper.S818StackHaarNormalizationAuditActual

end
