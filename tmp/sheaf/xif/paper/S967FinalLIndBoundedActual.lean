import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual
import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S967FinalLIndBoundedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual FinalL unit region: the transport of the qVFam canonical unit
reference O_hol.  This is a set on FinalLValuedCarrier, not a Real-Haar fiction. -/
noncomputable def finalLUnitRegion : Set (FinalLValuedCarrier T b) :=
  qVFamToLValued (l := l) T b '' S922O (l := l) T b

/-- Transported actual qVFam Ind images into the FinalL-valued packet. -/
noncomputable def finalLImageOfQVam (E : Set (qVFamTensorBlock T b)) :
    Set (FinalLValuedCarrier T b) :=
  qVFamToLValued (l := l) T b '' E

/-- Exact qVFam boundedness condition for the three actual Ind images. -/
def S967QVFamImagesBounded
    (E1 E2 E3 : Set (qVFamTensorBlock T b)) : Prop :=
  E1 ⊆ S922O (l := l) T b ∧ E2 ⊆ S922O (l := l) T b ∧
    E3 ⊆ S922O (l := l) T b

/-- Bounded qVFam images imply their FinalL transports lie in the FinalL unit
region. -/
theorem finalLImages_subset_unit
    {E1 E2 E3 : Set (qVFamTensorBlock T b)}
    (h : S967QVFamImagesBounded (l := l) T b E1 E2 E3) :
    finalLImageOfQVam (l := l) T b E1 ⊆ finalLUnitRegion (l := l) T b ∧
      finalLImageOfQVam (l := l) T b E2 ⊆ finalLUnitRegion (l := l) T b ∧
      finalLImageOfQVam (l := l) T b E3 ⊆ finalLUnitRegion (l := l) T b := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, h.1 hx, rfl⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, h.2.1 hx, rfl⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, h.2.2 hx, rfl⟩

/-- Exact data: actual nonempty qVFam Ind images plus boundedness. -/
structure S967FinalLIndBoundedData where
  image1 : Set (qVFamTensorBlock T b)
  image2 : Set (qVFamTensorBlock T b)
  image3 : Set (qVFamTensorBlock T b)
  image1_nonempty : image1.Nonempty
  image2_nonempty : image2.Nonempty
  image3_nonempty : image3.Nonempty
  images_bounded : S967QVFamImagesBounded (l := l) T b image1 image2 image3

def S967FinalLIndBoundedRequired : Prop :=
  Nonempty (S967FinalLIndBoundedData (l := l) T b)

end LeanFormal.IUT.XiFPaper.S967FinalLIndBoundedActual

end
