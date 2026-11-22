import tmp.sheaf.xif.paper.S809PaperLeastHullRootStackBridgeActual

noncomputable section
open scoped BigOperators NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S823StackHaarNormalizedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
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

/-- Candidate normalized stack Haar: scale rootStackHaar by the inverse unit-ball measure. -/
noncomputable def normalizedRootStackHaar : Measure (rootStackExtension (l := l) T b) :=
  (rootStackHaar (l := l) T b
    (Metric.closedBall (0 : rootStackExtension (l := l) T b) 1))⁻¹ •
      rootStackHaar (l := l) T b

/-- Log of the normalized unit ball. -/
noncomputable def normalizedRootStackUnitBallLog : Real :=
  Real.log
    ((normalizedRootStackHaar (l := l) T b
      (Metric.closedBall (0 : rootStackExtension (l := l) T b) 1)).toReal)

/-- Log of the normalized root ball. -/
noncomputable def normalizedRootStackRootBallLog : Real :=
  Real.log
    ((normalizedRootStackHaar (l := l) T b
      (Metric.closedBall (0 : rootStackExtension (l := l) T b)
        ‖(stackRootUnit (l := l) T b :
          rootStackExtension (l := l) T b)‖)).toReal)

/-- Exact normalized bridge target. -/
def NormalizedStackHaarBridge : Prop :=
  normalizedRootStackRootBallLog (l := l) T b =
    paperLeastLambdaOHullLog (l := l) T b mu

/-- Exact scaling formula with explicit d: root-ball log = d * log norm. -/
def StackHaarRootBallScalingFormula (d : Nat) : Prop :=
  normalizedRootStackRootBallLog (l := l) T b = (d : Real) *
    Real.log ‖(stackRootUnit (l := l) T b :
      rootStackExtension (l := l) T b)‖

/-- Exact root norm/log formula. -/
def StackRootUnitLogFormula : Prop :=
  Real.log ‖(stackRootUnit (l := l) T b :
      rootStackExtension (l := l) T b)‖ =
    paperQPilotLogLeast (l := l) T b

/-- Exact d-factor condition for the normalized bridge, conditional on the
scaling formula and the paper least-hull log formula. -/
theorem normalizedStackHaarBridge_iff_dFactor
    (d : Nat)
    (hscale : StackHaarRootBallScalingFormula (l := l) T b d)
    (hlog : StackRootUnitLogFormula (l := l) T b)
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b)) :
    NormalizedStackHaarBridge (l := l) T b mu ↔
      (d : Real) * paperQPilotLogLeast (l := l) T b =
        paperQPilotLogLeast (l := l) T b := by
  unfold NormalizedStackHaarBridge
  rw [hscale, hlog]
  rw [paperLeastLambdaOHullLog_eq_formula (l := l) T b mu D]
  unfold paperQPilotLogLeast
  rfl

/-- Exact d-factor condition. -/
def StackHaarDFactorCondition (d : Nat) : Prop :=
  (d : Real) * paperQPilotLogLeast (l := l) T b =
    paperQPilotLogLeast (l := l) T b

end LeanFormal.IUT.XiFPaper.S823StackHaarNormalizedActual

end
