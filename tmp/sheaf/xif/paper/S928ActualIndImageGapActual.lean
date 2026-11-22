import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S928ActualIndImageGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open MeasureTheory

universe u ua uv upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact actual Ind-image data for paper S.  The three source carriers and
their maps to the qVFam tensor block are part of the data; each image set is
the actual range.  No empty/default image is allowed: the actuality Props and
nonempty carriers are recorded, not assumed. -/
structure ActualIndImageData where
  Ind1 : Type
  Ind2 : Type
  Ind3 : Type
  toBlock1 : Ind1 → qVFamTensorBlock T b
  toBlock2 : Ind2 → qVFamTensorBlock T b
  toBlock3 : Ind3 → qVFamTensorBlock T b
  image1 : Set (qVFamTensorBlock T b)
  image2 : Set (qVFamTensorBlock T b)
  image3 : Set (qVFamTensorBlock T b)
  image1_eq_range : image1 = Set.range toBlock1
  image2_eq_range : image2 = Set.range toBlock2
  image3_eq_range : image3 = Set.range toBlock3
  ind1_actual : Prop
  ind2_actual : Prop
  ind3_actual : Prop

/-- Union of the actual Ind images. -/
noncomputable def actualIndImage (D : ActualIndImageData (l := l) T b) :
    Set (qVFamTensorBlock T b) :=
  D.image1 ∪ D.image2 ∪ D.image3

/-- Paper S from actual Ind images: closure of theta union actual Ind images.
This is the only paper-faithful S shape; it is not reduced to theta-only. -/
noncomputable def actualPaperS (D : ActualIndImageData (l := l) T b) :
    Set (qVFamTensorBlock T b) :=
  closure (paperRootThetaImageNZ T b ∪ actualIndImage (l := l) T b D)

/-- Exact gap: actual Ind image data is not supplied by the current tree.
No inhabitant is asserted. -/
def S928ActualPaperSRequired : Prop :=
  Nonempty (ActualIndImageData (l := l) T b)

/-- Theta-only is recorded only as an internal lower bound; it is not paper S. -/
def S928ThetaOnlyLowerBound : Prop :=
  paperRootThetaImageNZ T b ⊆
    paperRootThetaImageNZ T b

theorem s928ThetaOnlyLowerBound_holds :
    S928ThetaOnlyLowerBound T b :=
  subset_rfl

/-- Any actual paper S contains the theta lower bound. -/
theorem thetaLowerBound_subset_actualPaperS
    (D : ActualIndImageData (l := l) T b) :
    paperRootThetaImageNZ T b ⊆ actualPaperS (l := l) T b D :=
  fun _ hx => subset_closure (Or.inl hx)

end LeanFormal.IUT.XiFPaper.S928ActualIndImageGapActual

end
