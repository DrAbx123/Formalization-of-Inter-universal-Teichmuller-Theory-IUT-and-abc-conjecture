import tmp.sheaf.xif.paper.S733CorrectedPaperFinalCor312Actual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual

/-! # S744: paper-order replacement for S733 corrected hull log

S733CorrectedHullLog uses paperPerBThetaHullLog (S716 spectral c_norm).
Paper order replacement:
  S744CorrectedHullLog P T b := P.signedHullLogVolume = -paperPerBThetaHullLogPaperOrder.
Exact bridge: the spectral hull log equals the paper-order hull log.  The
coefficient bridge (spectral c_norm = order) is necessary; the hull-log
equality itself is not proved without S742. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S744PaperOrderReplacementActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S733CorrectedPaperFinalCor312Actual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable {X : Type*} {label : Type*} [Fintype label]
variable (P : PaperSignedHull X label)

/-- Paper-order per-b Theta hull log: coefficient order(q_v)/(2l). -/
noncomputable def paperPerBThetaHullLogPaperOrder : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- Paper-order replacement of S733CorrectedHullLog. -/
def S744CorrectedHullLog : Prop :=
  P.signedHullLogVolume = -paperPerBThetaHullLogPaperOrder (l := l) T b

/-- Exact coefficient bridge: spectral supply c_norm = paper order. -/
def PaperOrderCoefficientBridge : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient (l := l) T b =
    ((qVFamily T b).order : Real)

/-- Exact hull-log bridge needed for the replacement. -/
def PaperOrderHullLogBridge : Prop :=
  paperPerBThetaHullLog (l := l) T b =
    paperPerBThetaHullLogPaperOrder (l := l) T b

/-- If the paper-order hull log bridge holds, the S733 corrected hull log is
equivalent to the paper-order replacement. -/
theorem S733CorrectedHullLog_iff_S744_of_hullBridge
    (hbridge : PaperOrderHullLogBridge (l := l) T b) :
    S733CorrectedHullLog (l := l) P T b ↔
      S744CorrectedHullLog (l := l) T b P := by
  unfold S733CorrectedHullLog S744CorrectedHullLog
  rw [hbridge]

/-- Exact missing hypothesis for the replacement. -/
def S744PaperOrderHullLogBridgeRequired : Prop :=
  PaperOrderHullLogBridge (l := l) T b

end LeanFormal.IUT.XiFPaper.S744PaperOrderReplacementActualAdapted

end
