import tmp.sheaf.xif.paper.S928ActualIndImageGapActual

-- S943: exact actual Ind-image transfer to the qVFam block.
-- S937 currently does not compile (action type mismatch) and no S940 file
-- exists; the actual qVFam transport is therefore an explicit gap.
-- A conditional S928 ActualIndImageData constructor is provided.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S943ActualIndImageTransferActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S928ActualIndImageGapActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact transfer: three actual source carriers, their maps to qVFamTensorBlock,
range images, and actuality Props.  This is precisely the data S928 needs;
no source image is fabricated. -/
structure ActualIndImageTransfer where
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

def ActualIndImageTransferRequired : Prop :=
  Nonempty (ActualIndImageTransfer (l := l) T b)

/-- Conditional S928 ActualIndImageData from an exact transfer. -/
noncomputable def actualIndImageDataOfTransfer
    (X : ActualIndImageTransfer (l := l) T b) :
    ActualIndImageData (l := l) T b where
  Ind1 := X.Ind1
  Ind2 := X.Ind2
  Ind3 := X.Ind3
  toBlock1 := X.toBlock1
  toBlock2 := X.toBlock2
  toBlock3 := X.toBlock3
  image1 := X.image1
  image2 := X.image2
  image3 := X.image3
  image1_eq_range := X.image1_eq_range
  image2_eq_range := X.image2_eq_range
  image3_eq_range := X.image3_eq_range
  ind1_actual := X.ind1_actual
  ind2_actual := X.ind2_actual
  ind3_actual := X.ind3_actual

/-- Exact combined gap: actual source images plus qVFam transport.
S937 does not compile and S940 is absent, so this is not inhabited. -/
def S943ActualSourceAndTransportGap : Prop :=
  ActualIndImageTransferRequired (l := l) T b

theorem actualIndImageDataOfTransfer_nonempty
    (h : S943ActualSourceAndTransportGap (l := l) T b) :
    Nonempty (ActualIndImageData (l := l) T b) := by
  rcases h with ⟨X⟩
  exact ⟨actualIndImageDataOfTransfer (l := l) T b X⟩

#check ActualIndImageTransfer
#check actualIndImageDataOfTransfer
#check S943ActualSourceAndTransportGap

end LeanFormal.IUT.XiFPaper.S943ActualIndImageTransferActual

end