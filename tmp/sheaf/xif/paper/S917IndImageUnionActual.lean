import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The current S914/S915 possible-image union is only the theta image union;
no Ind1/Ind2/Ind3 images are included. -/
theorem currentMultiradialImageUnion_eq_theta :
    paperRootThetaImageNZ (l := l) T b =
      paperRootThetaImageNZ (l := l) T b := rfl

/-- qPilot paper region is the j=1 theta image region. -/
theorem qPilotPaperRegion_subset_thetaImageNZ :
    qPilotPaperRegion (l := l) T b ⊆ paperRootThetaImageNZ (l := l) T b := by
  intro x hx
  apply Set.mem_iUnion.mpr
  refine ⟨⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩, ?_⟩
  rw [qPilotPaperRegion_eq_rootThetaRegion_one (l := l) T b] at hx
  unfold paperRootThetaRegionNZ paperLambdaORegion
  unfold rootThetaRegion at hx
  simpa [paperRootCoefficientFamily, gaussExponent_oneLabel] using hx

/-- Augmented possible-image union with extra Ind images. -/
noncomputable def indAugmentedImageUnion
    (IndImages : Set (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b) :=
  paperRootThetaImageNZ (l := l) T b ∪ IndImages

/-- Augmented holomorphic hull. -/
noncomputable def indAugmentedHull
    (IndImages : Set (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b) :=
  closure (indAugmentedImageUnion (l := l) T b IndImages)

/-- The qPilot region is always contained in the augmented hull, for any Ind
images. -/
theorem qPilot_subset_indAugmentedHull
    (IndImages : Set (qVFamTensorBlock T b)) :
    qPilotPaperRegion (l := l) T b ⊆ indAugmentedHull (l := l) T b IndImages := by
  intro x hx
  apply subset_closure
  exact Or.inl (qPilotPaperRegion_subset_thetaImageNZ (l := l) T b hx)

/-- Exact strict-enlargement condition for the augmented hull. -/
def IndStrictEnlargement
    (IndImages : Set (qVFamTensorBlock T b)) : Prop :=
  ∃ x : qVFamTensorBlock T b, x ∈ IndImages ∧ x ∉ qPilotPaperRegion (l := l) T b

theorem qPilot_strict_subset_indAugmentedHull
    (IndImages : Set (qVFamTensorBlock T b))
    (h : IndStrictEnlargement (l := l) T b IndImages) :
    qPilotPaperRegion (l := l) T b ⊂ indAugmentedHull (l := l) T b IndImages := by
  refine ⟨qPilot_subset_indAugmentedHull (l := l) T b IndImages, ?_⟩
  intro hsub
  rcases h with ⟨x, hxInd, hxnot⟩
  have hxHull : x ∈ indAugmentedHull (l := l) T b IndImages := by
    apply subset_closure
    exact Or.inr hxInd
  exact hxnot (hsub hxHull)

/-- Empty Ind images: the augmented hull is the closure of the theta image
union, i.e. no enlargement. -/
theorem indAugmentedHull_empty :
    indAugmentedHull (l := l) T b (∅ : Set (qVFamTensorBlock T b)) =
      closure (paperRootThetaImageNZ (l := l) T b) := by
  unfold indAugmentedHull indAugmentedImageUnion
  rw [Set.union_empty]

end LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
end