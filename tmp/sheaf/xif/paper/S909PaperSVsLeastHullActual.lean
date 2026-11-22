import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.S907LVExToyActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S907LVExToyActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The model hull is the least lambda-O hull. -/
noncomputable def modelHull : Set (qVFamTensorBlock T b) :=
  paperLeastLambdaOHull T b

/-- The model hull is exactly the q-pilot paper region (lambda). -/
theorem modelHull_eq_qPilotPaperRegion :
    modelHull T b = qPilotPaperRegion T b :=
  paperLeastLambdaOHull_eq_minimal T b

/-- The model equality says S = lambda: no multiradial/Ind enlargement. -/
def ModelHullIsQPilot : Prop :=
  modelHull T b = qPilotPaperRegion T b

/-- Exact external paper S object and its strictness gap. -/
structure PaperSVsModelHullGap where
  paperS : Set (qVFamTensorBlock T b)
  model_subset_paperS : modelHull T b ⊆ paperS
  paperS_strict : ∃ x : qVFamTensorBlock T b, x ∈ paperS ∧ x ∉ modelHull T b

/-- Toy volume strictness under the explicit volume formula: paper S > lambda R. -/
theorem lvex_muLog_S_gt_muLog_R (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (hvol : VolumeFormula a b) :
    muLog (S a b) > muLog (R a b) :=
  muLog_S_gt_muLog_R a b ha hb hvol

end LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
end