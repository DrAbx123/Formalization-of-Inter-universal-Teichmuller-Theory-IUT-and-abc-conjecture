import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S915MultiradialHullCompareActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Paper multiradial possible-image union: all nonzero-label theta images. -/
noncomputable def paperMultiradialPossibleImageUnion : Set (qVFamTensorBlock T b) :=
  paperRootThetaImageNZ (l := l) T b

/-- Paper multiradial hull: closure of the multiradial possible-image union. -/
noncomputable def paperMultiradialHull : Set (qVFamTensorBlock T b) :=
  closure (paperMultiradialPossibleImageUnion (l := l) T b)

/-- Conditional inclusion: if the least hull is closed, the multiradial hull is
inside it. -/
theorem multiradialHull_subset_leastHull_of_closed
    (hclosed : IsClosed (paperLeastLambdaOHull (l := l) T b)) :
    paperMultiradialHull (l := l) T b ⊆ paperLeastLambdaOHull (l := l) T b := by
  unfold paperMultiradialHull
  apply closure_minimal
  · rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
    exact paperRootThetaImageNZ_subset_minimal (l := l) T b
  · exact hclosed

theorem leastHull_subset_multiradialHull :
    paperLeastLambdaOHull (l := l) T b ⊆ paperMultiradialHull (l := l) T b := by
  intro x hx
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b] at hx
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩, ?_⟩
  unfold paperRootThetaRegionNZ
  unfold paperLambdaORegion at hx ⊢
  convert hx using 1
  funext i
  simp [paperRootCoefficientFamily, gaussExponent_oneLabel]

/-- Exact closedness hypothesis needed for equality. -/
def PaperLeastHullClosed : Prop :=
  IsClosed (paperLeastLambdaOHull (l := l) T b)

/-- Equality of the multiradial hull and the least hull under the exact
closedness hypothesis. -/
theorem paperMultiradialHull_eq_leastHull_of_closed
    (h : PaperLeastHullClosed (l := l) T b) :
    paperMultiradialHull (l := l) T b = paperLeastLambdaOHull (l := l) T b :=
  Set.Subset.antisymm
    (multiradialHull_subset_leastHull_of_closed (l := l) T b h)
    (leastHull_subset_multiradialHull (l := l) T b)

/-- Strict-enlargement predicate is false for this actual multiradial hull. -/
def MultiradialStrictlyLarger : Prop :=
  paperLeastLambdaOHull (l := l) T b ⊂ paperMultiradialHull (l := l) T b

theorem multiradialStrictlyLarger_false_of_closed
    (h : PaperLeastHullClosed (l := l) T b) :
    ¬ MultiradialStrictlyLarger (l := l) T b := by
  intro hs
  exact hs.2 (le_of_eq (paperMultiradialHull_eq_leastHull_of_closed (l := l) T b h))

end LeanFormal.IUT.XiFPaper.S915MultiradialHullCompareActualAdapted

end
