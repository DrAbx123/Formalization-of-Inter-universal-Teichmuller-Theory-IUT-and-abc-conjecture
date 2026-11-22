import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual
import tmp.sheaf.xif.paper.S917IndImageUnionActual
import tmp.sheaf.xif.paper.S956TensorPacketLogVolumeExactActual
/-! # S971: paper possible images are lambda-O regions, not points
Audit: paperRootThetaImageNZ is a union of paperLambdaORegion (lambda-O)
regions (S793), and qPilotPaperRegion is exactly the j=1 region, hence
qPilotPaperRegion ⊆ paperRootThetaImageNZ (S917, actual).  On the tensor packet
we therefore take the image of the whole region under qVFamToLValued, not a
point image.  This gives direct union/hull containment, with no point-set
approximation. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S971TensorRegionImageActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open MeasureTheory Topology
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Tensor image of the whole paper lambda-O possible-image union. -/
noncomputable def tensorThetaRegionImage : Set (FinalLValuedCarrier T b) :=
  qVFamToLValued (l := l) T b '' paperRootThetaImageNZ (l := l) T b
/-- Actual region-image union: region image plus the actual Ind point images. -/
noncomputable def tensorThetaRegionIndUnion : Set (FinalLValuedCarrier T b) :=
  tensorThetaRegionImage (l := l) T b ∪ thetaImageIndUnion (l := l) T b
/-- Actual qPilot image is contained in the region image, not in points. -/
theorem qPilotPaperImage_subset_tensorRegionImage :
    qPilotPaperImageInLValued (l := l) T b ⊆
      tensorThetaRegionImage (l := l) T b :=
  Set.image_mono (qPilotPaperRegion_subset_thetaImageNZ (l := l) T b)
theorem qPilotPaperImage_subset_tensorRegionIndUnion :
    qPilotPaperImageInLValued (l := l) T b ⊆
      tensorThetaRegionIndUnion (l := l) T b :=
  fun x hx => Or.inl (qPilotPaperImage_subset_tensorRegionImage (l := l) T b hx)
/-- Region-image hull under the S956 carrier topology. -/
noncomputable def tensorRegionHull
    (D : FinalLTensorLogVolumeData (l := l) T b) :
    Set (FinalLValuedCarrier T b) := by
  letI := D.topologicalSpace
  exact closure (tensorThetaRegionIndUnion (l := l) T b)
/-- Actual hull containment: region image ⊆ closure of the region union. -/
theorem qPilotPaperImage_subset_tensorRegionHull
    (D : FinalLTensorLogVolumeData (l := l) T b) :
    qPilotPaperImageInLValued (l := l) T b ⊆
      tensorRegionHull (l := l) T b D := by
  letI : TopologicalSpace (FinalLValuedCarrier T b) := D.topologicalSpace
  intro x hx
  exact subset_closure
    (qPilotPaperImage_subset_tensorRegionIndUnion (l := l) T b hx)
end LeanFormal.IUT.XiFPaper.S971TensorRegionImageActual
