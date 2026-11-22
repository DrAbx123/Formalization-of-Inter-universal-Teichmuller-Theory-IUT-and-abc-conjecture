import tmp.sheaf.xif.paper.S917IndImageUnionActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotEmptyAugmentedActualAdapted
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: q-pilot region is contained in the empty-Ind augmented hull. -/
theorem S3128Stage1QPilot_subset_emptyAugmentedHull :
    qPilotPaperRegion (l := l) T b ⊆
      indAugmentedHull (l := l) T b (∅ : Set (qVFamTensorBlock T b)) := by
  rw [indAugmentedHull_empty (l := l) T b]
  intro x hx
  exact subset_closure
    (qPilotPaperRegion_subset_thetaImageNZ (l := l) T b hx)

#check S3128Stage1QPilot_subset_emptyAugmentedHull
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotEmptyAugmentedActualAdapted