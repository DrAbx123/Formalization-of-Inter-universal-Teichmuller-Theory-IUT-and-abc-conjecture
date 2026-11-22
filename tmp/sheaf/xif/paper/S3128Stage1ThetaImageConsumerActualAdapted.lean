import tmp.sheaf.xif.paper.S917IndImageUnionActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ThetaImageConsumerActualAdapted
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1ThetaImage_subset_augmentedHull
    (IndImages : Set (qVFamTensorBlock T b)) :
    paperRootThetaImageNZ (l := l) T b ⊆
      indAugmentedHull (l := l) T b IndImages := by
  intro x hx
  exact subset_closure (Or.inl hx)

theorem S3128Stage1ThetaImage_subset_emptyAugmentedHull :
    paperRootThetaImageNZ (l := l) T b ⊆
      indAugmentedHull (l := l) T b (∅ : Set (qVFamTensorBlock T b)) :=
  S3128Stage1ThetaImage_subset_augmentedHull (l := l) T b ∅

#check S3128Stage1ThetaImage_subset_augmentedHull
#check S3128Stage1ThetaImage_subset_emptyAugmentedHull
end LeanFormal.IUT.XiFPaper.S3128Stage1ThetaImageConsumerActualAdapted