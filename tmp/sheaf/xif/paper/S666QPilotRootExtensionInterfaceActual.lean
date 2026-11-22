import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

/-! # S666: qPilot -> RootExtensionProductCarrier comparison interface

The qPilot classical region lives on the bad-place tensor block, while
`RootExtensionProductCarrier T` is the product of root extension fields.
There is no actual map between these two carriers in the tree; this file
records the actual log data and the exact containment/log comparison interface
without fabricating a carrier map.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S666QPilotRootExtensionInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)

/-- Actual qPilot classical region on the bad-place tensor block. -/
noncomputable def qPilotRegion :
    Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) :=
  qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm

/-- Actual qPilot classical log from the qVFam tensor data. -/
noncomputable def qPilotLog : Real :=
  qPilotClassicalLog (qVFamTensorPlaces T b) qVFamTensorTuple
    Measure.addHaar cNorm dataNorm

/-- Actual root-extension product image hull. -/
noncomputable def rootImageHull : Set (RootExtensionProductCarrier T) :=
  rootExtensionProductImageHull T

/-- Actual normalized log of the root-extension image hull. -/
noncomputable def rootImageLog : Real :=
  rootExtensionProductImageHullLog T

/-- Exact interface: both actual sets/logs and the missing containment/log
comparison.  `containment` is an explicit proposition, not a fabricated map. -/
structure QPilotRootExtensionInterface where
  qPilot_set : Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)
  qPilot_set_eq : qPilot_set = qPilotRegion (l := l) T b cNorm
  qPilot_log : Real
  qPilot_log_eq : qPilot_log = qPilotLog (l := l) T b cNorm dataNorm
  rootImage_set : Set (RootExtensionProductCarrier T)
  rootImage_set_eq : rootImage_set = rootImageHull (l := l) T
  rootImage_log : Real
  rootImage_log_eq : rootImage_log = rootImageLog (l := l) T
  containment : Prop
  log_comparison : containment → qPilot_log ≤ rootImage_log

/-- The exact comparison proposition (no carrier map is asserted). -/
def QPilotRootExtensionComparisonObstacle : Prop :=
  qPilotLog (l := l) T b cNorm dataNorm ≤ rootImageLog (l := l) T

/-- Conditional construction of the interface from an explicit comparison. -/
noncomputable def interfaceOfComparison
    (h : qPilotLog (l := l) T b cNorm dataNorm ≤ rootImageLog (l := l) T) :
    QPilotRootExtensionInterface (l := l) T b cNorm dataNorm where
  qPilot_set := qPilotRegion (l := l) T b cNorm
  qPilot_set_eq := rfl
  qPilot_log := qPilotLog (l := l) T b cNorm dataNorm
  qPilot_log_eq := rfl
  rootImage_set := rootImageHull (l := l) T
  rootImage_set_eq := rfl
  rootImage_log := rootImageLog (l := l) T
  rootImage_log_eq := rfl
  containment := qPilotLog (l := l) T b cNorm dataNorm ≤ rootImageLog (l := l) T
  log_comparison := by intro hc; exact hc

def QPilotRootExtensionInterfaceRequired : Prop :=
  Nonempty (QPilotRootExtensionInterface (l := l) T b cNorm dataNorm)

end LeanFormal.IUT.XiFPaper.S666QPilotRootExtensionInterfaceActual
end
