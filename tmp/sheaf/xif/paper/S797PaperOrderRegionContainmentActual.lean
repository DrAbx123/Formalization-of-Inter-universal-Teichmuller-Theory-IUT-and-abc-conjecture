import tmp.sheaf.xif.paper.S785PaperOrderThetaHullBypassActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S797PaperOrderRegionContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.S775PaperOrderQPilotCorrectionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Paper-order qPilot region: coefficient order/(2l). -/
noncomputable def paperQPilotRegionPaperOrder :
    Set (qVFamTensorBlock T b) :=
  qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b)

/-- The paper-order qPilot region is contained in the paper root-theta hull. -/
theorem paperQPilotRegionPaperOrder_subset_hull :
    paperQPilotRegionPaperOrder T b ⊆ paperRootThetaHull T b := by
  unfold paperQPilotRegionPaperOrder paperRootThetaHull
  exact qPilotClassicalRegion_subset_rootHull
    (l := l) (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (cNorm := paperRootCoefficientFamily T b)
    (cRoot := paperRootCoefficientFamily T b)
    (fun _ => le_rfl) (oneLabel l) (gaussExponent_oneLabel l)

/-- Exact region-containment target. -/
def PaperOrderRegionContainment : Prop :=
  paperQPilotRegionPaperOrder T b ⊆ paperRootThetaHull T b

theorem paperOrderRegionContainment_actual :
    PaperOrderRegionContainment (l := l) T b :=
  paperQPilotRegionPaperOrder_subset_hull T b

end LeanFormal.IUT.XiFPaper.S797PaperOrderRegionContainmentActual

end
