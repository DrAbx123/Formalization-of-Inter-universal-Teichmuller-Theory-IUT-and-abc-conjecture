import tmp.sheaf.xif.paper.S775PaperOrderQPilotCorrectionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

/-! # S785: bypass spectral bridge with paper-order theta hull

The paper-order Theta hull is built directly from
  paperRootCoefficientFamily = order(q_v)/(2l),
not from the spectral generator-supply c_norm.  Therefore
  paperThetaHullLogPaperOrder = paperRootThetaHullLog
is actual without PaperThetaHullBridge.  The qPilot paper-order side is
order/(2l)*log p.  The remaining comparison is exact: PaperTargetPaperOrder. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S785PaperOrderThetaHullBypassActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S775PaperOrderQPilotCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The paper-order Theta hull log is the actual paperRootThetaHullLog. -/
theorem paperThetaHullLogPaperOrder_eq_paperRoot :
    paperThetaHullLogPaperOrder (l := l) T b =
      paperRootThetaHullLog (l := l) T b Measure.addHaar := rfl

/-- Paper root coefficient is order/(2l), independent of spectral c_norm. -/
theorem paperRootCoefficientFamily_eq_order_div :
    paperRootCoefficientFamily (l := l) T b () =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := rfl

/-- The paper qPilot coefficient is order/(2l). -/
theorem paperQPilotCoefficient_eq_order_div :
    paperQPilotCoefficientPaperOrder (l := l) T b () =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := rfl

/-- Exact remaining paper-order comparison target. -/
def S785PaperTargetRequired : Prop :=
  PaperTargetPaperOrder (l := l) T b

/-- PaperTargetPaperOrder is stated directly in paper-order hull logs; it
does not require the spectral PaperThetaHullBridge. -/
theorem s785Target_iff :
    S785PaperTargetRequired (l := l) T b ↔
      paperQPilotLogPaperOrder (l := l) T b ≤
        paperRootThetaHullLog (l := l) T b Measure.addHaar := by
  unfold S785PaperTargetRequired PaperTargetPaperOrder
    paperThetaHullLogPaperOrder
  rfl

end LeanFormal.IUT.XiFPaper.S785PaperOrderThetaHullBypassActual

end
