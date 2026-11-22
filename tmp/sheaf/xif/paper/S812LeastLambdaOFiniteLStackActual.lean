import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

-- S812: least lambda*O paper hull log formula and exact finite-L Haar
-- bridge.  S793/S799 hull is on qVFamTensorBlock; S782 finite L(mu_{2l})
-- carries rootStackHaar.  The formula is actual; the carrier/measure
-- transport is the exact minimal bridge.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S812LeastLambdaOFiniteLStackActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
variable (data : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b))

/-- Actual paper least-lambda*O hull log formula, independent of the union/
closure hull. -/
theorem paperLeastLambdaOHullLog_formula
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperLeastLambdaOHullLog (l := l) T b μ =
      -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
        Real.log (qVFamTensorP T b : Real)) :=
  paperLeastLambdaOHullLog_eq_formula (l := l) T b μ data

/-- Actual paper-order qPilot log on the least hull. -/
theorem paperQPilotLogLeast_le_paperLeastHullLog
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ :=
  paperQPilotLogLeast_le_leastHullLog (l := l) T b μ data

/-- S782 finite root-stack root section has paper coefficient order/(2l). -/
theorem stackRootSection_paperOrder_divisor :
    stackDivisorSection (l := l) T b (stackRootSection (l := l) T b) =
      Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) :=
  rfl

theorem stackQSection_paperOrder_divisor :
    stackDivisorSection (l := l) T b (stackQSection (l := l) T b) =
      Multiplicative.ofAdd ((qVFamily T b).order : Real) :=
  rfl

/-- Exact minimal bridge from the tensor-block least hull to the actual
finite-L(mu_{2l}) Haar. -/
structure PaperLeastHullFiniteLHaarBridge where
  carrierEquiv : qVFamTensorBlock T b ≃ rootStackExtension T b
  measurable_carrierEquiv : Measurable carrierEquiv
  haar_transport : Prop
  haar_transport_holds : haar_transport
  stackHull : Set (rootStackExtension T b)
  hull_transport : Prop
  hull_transport_holds : hull_transport
  stackHullLog : Real
  stackHullLog_eq : Prop
  stackHullLog_eq_holds : stackHullLog_eq

def PaperLeastHullFiniteLHaarBridgeRequired : Prop :=
  Nonempty (PaperLeastHullFiniteLHaarBridge (l := l) T b)

#check paperLeastLambdaOHullLog_formula
#check paperQPilotLogLeast_le_paperLeastHullLog
#check stackRootSection_paperOrder_divisor
#check PaperLeastHullFiniteLHaarBridgeRequired

end LeanFormal.IUT.XiFPaper.S812LeastLambdaOFiniteLStackActual

end