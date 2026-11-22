import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S917IndImageUnionActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullAugmentedConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHull_augmentedHull_empty_subset
    (D : PaperIndImageData T b) :
    indAugmentedHull T b (∅ : Set (qVFamTensorBlock T b)) ⊆
      paperSHull T b D := by
  rw [indAugmentedHull_empty]
  intro x hx
  exact closure_mono (fun _ hy => Or.inl hy) hx

theorem S3128Stage1PaperSHull_augmentedHull_subset
    (D : PaperIndImageData T b)
    (IndImages : Set (qVFamTensorBlock T b))
    (hInd : IndImages ⊆ D.indImage) :
    indAugmentedHull T b IndImages ⊆ paperSHull T b D := by
  intro x hx
  exact closure_mono (fun y hy => by
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (hInd hy)) hx

#check S3128Stage1PaperSHull_augmentedHull_empty_subset
#check S3128Stage1PaperSHull_augmentedHull_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullAugmentedConsumerActual