import tmp.sheaf.xif.paper.S957TensorClosureContainmentActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S975DensityRegionImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData T b)

/-- L-valued image of the theta region at a label: the region-image route. -/
noncomputable def rootThetaRegionImageInLValued
    (j : SignedLabel l.value) : Set (FinalLValuedCarrier T b) :=
  qVFamToLValued T b ''
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b) j

/-- Union of all actual theta region images in the L-valued tensor packet. -/
noncomputable def paperPossibleRegionImageUnion
    : Set (FinalLValuedCarrier T b) :=
  ⋃ j : SignedLabel l.value, rootThetaRegionImageInLValued (l := l) T b j

/-- Actual region-image containment: the qPilot image is the j=1 theta
region image, so it lies in the possible-region union. -/
theorem qPilotRegionImage_subset_regionUnion :
    qVFamToLValued T b '' qPilotPaperRegion (l := l) T b ⊆
      paperPossibleRegionImageUnion (l := l) T b := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [qPilotPaperRegion_eq_rootThetaRegion_one (l := l) T b] at hx
  exact Set.mem_iUnion.mpr ⟨oneLabel l, ⟨x, hx, rfl⟩⟩

/-- Exact remaining region-image condition: the possible-region union is
contained in the paper tensor hull. -/
def S975RegionImageSubsetPaperTensorHull : Prop :=
  paperPossibleRegionImageUnion (l := l) T b ⊆
    paperTensorHull (l := l) T b D

/-- Region-image subset implies S957 density. -/
theorem s957ThetaImageDenseInQPilot_of_regionImageSubset
    (h : S975RegionImageSubsetPaperTensorHull (l := l) T b D) :
    S957ThetaImageDenseInQPilot (l := l) T b D := by
  intro y hy
  exact h (qPilotRegionImage_subset_regionUnion (l := l) T b hy)

/-- Exact S957 density gap, retained as a Prop. -/
def S975DensityExactGap : Prop :=
  S957ThetaImageDenseInQPilot (l := l) T b D

end LeanFormal.IUT.XiFPaper.S975DensityRegionImageActual

end
