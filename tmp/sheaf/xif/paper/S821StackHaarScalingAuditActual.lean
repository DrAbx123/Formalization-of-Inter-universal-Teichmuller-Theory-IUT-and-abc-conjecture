import tmp.sheaf.xif.paper.S818StackHaarNormalizationAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S821StackHaarScalingAuditActual

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
open LeanFormal.IUT.XiFPaper.S818StackHaarNormalizationAuditActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Log Haar of the unit ball in the finite root-stack extension. -/
noncomputable def stackHaarUnitBallLog : Real :=
  Real.log
    ((rootStackHaar (l := l) T b
      (Metric.closedBall (0 : rootStackExtension (l := l) T b) 1)).toReal)

/-- Exact normalized scaling factor between the root ball and the unit ball. -/
noncomputable def stackHaarBallScalingFactor : Real :=
  stackHaarBallLog (l := l) T b - stackHaarUnitBallLog (l := l) T b

/-- Exact reformulation of the bridge in terms of the actual unit-ball Haar
and the scaling factor; no scaling value is asserted. -/
theorem stackHaarNormalizationBridge_iff_scaling :
    StackHaarNormalizationBridge (l := l) T b mu ↔
      stackHaarBallScalingFactor (l := l) T b +
        stackHaarUnitBallLog (l := l) T b =
      paperLeastLambdaOHullLog (l := l) T b mu := by
  rw [stackHaarNormalizationBridge_iff (l := l) T b mu]
  unfold stackHaarBallScalingFactor stackHaarBallLog stackHaarUnitBallLog
  ring_nf

/-- Conditional bridge from an explicit unit-ball log and an explicit scaling
factor. -/
theorem stackHaarNormalizationBridge_of_unitAndScaling
    (hunit : stackHaarUnitBallLog (l := l) T b = 0)
    (hscale : stackHaarBallScalingFactor (l := l) T b =
      paperLeastLambdaOHullLog (l := l) T b mu) :
    StackHaarNormalizationBridge (l := l) T b mu := by
  rw [stackHaarNormalizationBridge_iff_scaling (l := l) T b mu]
  rw [hunit, hscale]
  ring

/-- Exact minimal normalization datum: the actual root-ball scaling factor
together with the unit-ball log.  No Haar normalization is faked. -/
def StackHaarNormalizationScalingDatum : Prop :=
  stackHaarBallScalingFactor (l := l) T b +
      stackHaarUnitBallLog (l := l) T b =
    paperLeastLambdaOHullLog (l := l) T b mu

end LeanFormal.IUT.XiFPaper.S821StackHaarScalingAuditActual

end
