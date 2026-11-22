import tmp.sheaf.xif.paper.S733CorrectedPaperFinalCor312Actual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.S739PaperOrderThetaHullActual

/-! # S761: S733/S734/S739 dependencies and surrogate audit

S734/S739 do not use the old `PaperRootHullFormulaGap`.  They use the actual
root hull definitions and an explicit coefficient bridge
  spectral c_norm = order(q_v).
S733 uses paperPerBThetaHullLog (S716 spectral c_norm), so its
S733CorrectedHullLog is a spectral surrogate unless that bridge holds.
The paper-order replacement needs the hull-log bridge
  paperPerBThetaHullLog = paperPerBThetaHullLogPaperOrder.
No fake gap is supplied. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S761S733SurrogateAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S733CorrectedPaperFinalCor312Actual
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

/-- Paper-order per-b Theta hull log. -/
noncomputable def paperPerBThetaHullLogPaperOrder : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- S733 replacement: signed hull log based on paper-order hull log. -/
def S761PaperOrderHullLog : Prop :=
  P.signedHullLogVolume = -paperPerBThetaHullLogPaperOrder (l := l) T b

/-- Exact spectral-vs-paper coefficient bridge. -/
def S761CoefficientBridge : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient (l := l) T b =
    ((qVFamily T b).order : Real)

/-- Exact spectral-vs-paper hull-log bridge. -/
def S761HullLogBridge : Prop :=
  paperPerBThetaHullLog (l := l) T b =
    paperPerBThetaHullLogPaperOrder (l := l) T b

/-- With the hull-log bridge, S733 corrected hull log is the paper-order one. -/
theorem s733_iff_paperOrder_of_bridge
    (h : S761HullLogBridge (l := l) T b) :
    S733CorrectedHullLog (l := l) P T b ↔ S761PaperOrderHullLog (l := l) T b P := by
  unfold S733CorrectedHullLog S761PaperOrderHullLog
  rw [h]

/-- Exact strengthened gap: coefficient bridge plus hull-log bridge. -/
structure S761StrengthenedGap where
  coefficient : S761CoefficientBridge (l := l) T b
  hullLog : S761HullLogBridge (l := l) T b

/-- Exact requirement for the paper-order replacement. -/
def S761PaperOrderReplacementRequired : Prop :=
  Nonempty (S761StrengthenedGap (l := l) T b)

end LeanFormal.IUT.XiFPaper.S761S733SurrogateAuditActual

end
