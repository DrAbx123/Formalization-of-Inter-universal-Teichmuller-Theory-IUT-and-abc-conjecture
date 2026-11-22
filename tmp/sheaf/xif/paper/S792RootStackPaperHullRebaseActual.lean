import tmp.sheaf.xif.paper.S790StackToPaperQPilotThetaActual
import tmp.sheaf.xif.paper.S733CorrectedPaperFinalCor312Actual

/-! # S792: rebase paper theta hull to finite root-stack paper order

S733/S716 use spectral perBThetaHullLog = spectral c_norm/(2l).  The actual
paper hull is the paper-root hull at coefficient order/(2l), as constructed
from the S782 finite root-stack extension and S790:
  paperRootThetaHull, paperRootThetaHullLog.
S792CorrectedHullLog replaces the spectral signed hull log by this actual
paper-root hull log.  The quantum comparison target is S790.PaperStackTarget.
The spectral S733 hull is a surrogate unless the spectral/order bridge holds.
No fake Haar equality is supplied. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S792RootStackPaperHullRebaseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S790StackToPaperQPilotThetaActual
open LeanFormal.IUT.XiFPaper.S733CorrectedPaperFinalCor312Actual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
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

/-- Paper-root hull log at order/(2l), from the root-stack paper carrier. -/
noncomputable def paperRootHullLogRebased : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- Paper-root hull log is exactly the actual paperRootThetaHullLog. -/
theorem paperRootHullLogRebased_eq :
    paperRootHullLogRebased (l := l) T b =
      paperRootThetaHullLog (l := l) T b Measure.addHaar := rfl

/-- S733 replacement: signed hull log uses the paper-root hull, not spectral. -/
def S792CorrectedHullLog : Prop :=
  P.signedHullLogVolume = -paperRootHullLogRebased (l := l) T b

/-- Actual paper-order qPilot/hull target from S790. -/
def S792PaperTarget : Prop :=
  PaperStackTarget (l := l) T b

/-- The target is exactly paper qPilot log <= paper-root hull log. -/
theorem S792PaperTarget_iff :
    S792PaperTarget (l := l) T b ↔
      paperStackQPilotLog (l := l) T b ≤
        paperRootThetaHullLog (l := l) T b Measure.addHaar := by
  unfold S792PaperTarget PaperStackTarget
  rfl

/-- Exact remaining Haar positivity/finiteness bridge for the paper target. -/
def S792PaperHaarBridgeRequired : Prop :=
  PaperStackHaarBridge (l := l) T b

end LeanFormal.IUT.XiFPaper.S792RootStackPaperHullRebaseActual

end
